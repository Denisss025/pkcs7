package pkcs7

import (
	"bytes"
	"errors"
	"io"
	"sync"
)

var (
	bufPool = sync.Pool{New: func() interface{} {
		return new(bytes.Buffer)
	}}

	ehwPool = sync.Pool{New: func() interface{} {
		return new(errHandlerWriter)
	}}

	ErrBerIsEmpty           = errors.New("ber2der: input ber is empty")
	ErrTagLenTooLong        = errors.New("ber2der: BER tag length too long")
	ErrTagLenNegative       = errors.New("ber2der: BER tag length is negative")
	ErrTagLenHasLeadingZero = errors.New("ber2der: BER tag length has leading zero")
	ErrTagLenOverflow       = errors.New("ber2der: BER tag length is more than available data")
	ErrInvalidFormat        = errors.New("ber2der: Invalid BER format")
)

type asn1Object interface {
	EncodeTo(io.Writer) error
}

type asn1Structured struct {
	tagBytes []byte
	content  []asn1Object
}

type errHandlerWriter struct {
	io.Writer
	Err error
}

func (w *errHandlerWriter) Write(p []byte) (n int, err error) {
	if err = w.Err; err != nil {
		return
	}
	n, err = w.Writer.Write(p)
	w.Err = err
	return
}

func AcquireErrorHandler(w io.Writer) *errHandlerWriter {
	ehw := ehwPool.Get().(*errHandlerWriter)
	ehw.Writer = w
	ehw.Err = nil
	return ehw
}

func (w *errHandlerWriter) Release() error {
	err := w.Err
	ehwPool.Put(w)
	return err
}

func (s *asn1Structured) EncodeTo(out io.Writer) error {
	inner := bufPool.Get().(*bytes.Buffer)
	inner.Reset()
	defer bufPool.Put(inner)

	for _, obj := range s.content {
		err := obj.EncodeTo(inner)
		if err != nil {
			return err
		}
	}
	errorHandler := AcquireErrorHandler(out)
	defer errorHandler.Release()

	errorHandler.Write(s.tagBytes)
	if _, err := encodeLength(errorHandler, int64(inner.Len())); err != nil {
		return err
	}
	errorHandler.Write(inner.Bytes())
	err := errorHandler.Err
	return err
}

type asn1Primitive struct {
	tagBytes []byte
	content  []byte
}

func (p asn1Primitive) EncodeTo(out io.Writer) error {
	errorHandler := AcquireErrorHandler(out)
	defer errorHandler.Release()
	errorHandler.Write(p.tagBytes)
	if _, err := encodeLength(out, int64(len(p.content))); err != nil {
		return err
	}
	errorHandler.Write(p.content)
	err := errorHandler.Err
	return err
}

func ber2der(dst io.Writer, ber io.Reader) error {
	//fmt.Printf("--> ber2der: Transcoding %d bytes\n", len(ber))
	if obj, _, err := readObject(ber); err != nil {
		return err
	} else {
		return obj.EncodeTo(dst)
	}
	// if offset < len(ber) {
	//	return nil, fmt.Errorf("ber2der: Content longer than expected. Got %d, expected %d", offset, len(ber))
	//}

}

// encodes the length in DER format
// If the length fits in 7 bits, the value is encoded directly.
//
// Otherwise, the number of bytes to encode the length is first determined.
// This number is likely to be 4 or less for a 32bit length. This number is
// added to 0x80. The length is encoded in big endian encoding follow after
//
// Examples:
//  length | byte 1 | bytes n
//  0      | 0x00   | -
//  120    | 0x78   | -
//  200    | 0x81   | 0xC8
//  500    | 0x82   | 0x01 0xF4
//
func encodeLength(out io.Writer, length int64) (int, error) {
	var buf64 = [9]byte{0x88,
		byte(length >> 0x38), byte(length >> 0x30),
		byte(length >> 0x28), byte(length >> 0x20),
		byte(length >> 0x18), byte(length >> 0x10),
		byte(length >> 0x08), byte(length),
	}

	buf := buf64[:]
	for buf[1] == 0 && len(buf) > 2 {
		buf[1] = buf[0] - 1
		buf = buf[1:]
	}

	if len(buf) == 2 && buf[1] < 0x80 {
		buf = buf[1:]
	}

	return out.Write(buf)
}

func readObject(r io.Reader) (asn1Object, int, error) {
	buf := bufPool.Get().(*bytes.Buffer)
	buf.Reset()
	defer bufPool.Put(buf)

	if n, err := io.Copy(buf, r); err != nil {
		return nil, 0, err
	} else if n == 0 {
		return nil, 0, ErrBerIsEmpty
	}
	//fmt.Printf("\n====> Starting readObject at offset: %d\n\n", offset)
	offset := 0
	ber := make([]byte, buf.Len())
	io.ReadFull(buf, ber)
	b := ber[offset]
	offset++
	// Tag == last 5 bits
	if b&0x1F == 0x1F {
		tag := byte(0)
		for ber[offset] >= 0x80 {
			tag = tag*128 + ber[offset] - 0x80
			offset++
		}
		tag = tag*128 + ber[offset] - 0x80
		offset++
	}
	tagEnd := offset

	kind := b & 0x20
	/*
		if kind == 0 {
			fmt.Print("--> Primitive\n")
		} else {
			fmt.Print("--> Constructed\n")
		}
	*/
	// read length
	var length int
	l := ber[offset]
	offset++
	hack := 0
	if l > 0x80 {
		numberOfBytes := (int)(l & 0x7F)
		if numberOfBytes > 4 { // int is only guaranteed to be 32bit
			return nil, 0, ErrTagLenTooLong
		}
		length = (int)(ber[offset])
		if numberOfBytes == 4 && length > 0x7F {
			return nil, 0, ErrTagLenNegative
		}
		if length == 0x0 {
			return nil, 0, ErrTagLenHasLeadingZero
		}
		offset++
		numberOfBytes--
		//fmt.Printf("--> (compute length) indicator byte: %x\n", l)
		//fmt.Printf("--> (compute length) length bytes: % X\n", ber[offset:offset+numberOfBytes])
		for i := 0; i < numberOfBytes; i++ {
			length = length*256 + (int)(ber[offset])
			offset++
		}
	} else if l == 0x80 {
		// find length by searching content
		markerIndex := bytes.LastIndex(ber[offset:], []byte{0x0, 0x0})
		if markerIndex == -1 {
			return nil, 0, ErrInvalidFormat
		}
		length = markerIndex
		hack = 2
		//fmt.Printf("--> (compute length) marker found at offset: %d\n", markerIndex+offset)
	} else {
		length = (int)(l)
	}

	//fmt.Printf("--> length        : %d\n", length)
	contentEnd := offset + length
	if contentEnd > len(ber) {
		return nil, 0, ErrTagLenOverflow
	}
	//fmt.Printf("--> content start : %d\n", offset)
	//fmt.Printf("--> content end   : %d\n", contentEnd)
	//fmt.Printf("--> content       : % X\n", ber[offset:contentEnd])
	var obj asn1Object
	if kind == 0 {
		obj = asn1Primitive{
			tagBytes: ber[:tagEnd],
			content:  ber[offset:contentEnd],
		}
	} else {
		var subObjects []asn1Object
		var err error
		var subObj asn1Object
		for offset < contentEnd {
			subObj, length, err = readObject(bytes.NewReader(ber[offset:contentEnd]))
			if err != nil {
				return nil, 0, err
			}
			offset += length
			subObjects = append(subObjects, subObj)
		}
		obj = &asn1Structured{
			tagBytes: ber[:tagEnd],
			content:  subObjects,
		}
	}

	return obj, contentEnd + hack, nil
}
