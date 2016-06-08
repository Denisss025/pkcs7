// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package asn1 implements parsing of DER-encoded ASN.1 data structures,
// as defined in ITU-T Rec X.690.
//
// See also ``A Layman's Guide to a Subset of ASN.1, BER, and DER,''
// http://luca.ntop.org/Teaching/Appunti/asn1.html.
package pkcs7

// ASN.1 is a syntax for specifying abstract objects and BER, DER, PER, XER etc
// are different encoding formats for those objects. Here, we'll be dealing
// with DER, the Distinguished Encoding Rules. DER is used in X.509 because
// it's fast to parse and, unlike BER, has a unique encoding for every object.
// When calculating hashes over objects, it's important that the resulting
// bytes be the same at both ends and DER removes this margin of error.
//
// ASN.1 is very complex and this package doesn't attempt to implement
// everything by any means.

import (
	"bytes"
	"encoding/asn1"
	"errors"
	"fmt"
	"io"
	"math/big"
	"reflect"
	"time"
	"unicode/utf8"
)

// BOOLEAN

func parseBool(data []byte) (ret bool, err error) {
	if len(data) != 1 {
		err = asn1.SyntaxError{"invalid boolean"}
		return
	}

	// DER demands that "If the encoding represents the boolean value TRUE,
	// its single contents octet shall have all eight bits set to one."
	// Thus only 0 and 255 are valid encoded values.
	switch data[0] {
	case 0:
		ret = false
	case 0xff:
		ret = true
	default:
		err = asn1.SyntaxError{"invalid boolean"}
	}

	return
}

// INTEGER

// checkInteger returns nil if the given bytes are a valid DER-encoded
// INTEGER and an error otherwise.
func checkInteger(data []byte) error {
	if len(data) == 0 {
		return asn1.StructuralError{"empty integer"}
	}
	if len(data) == 1 {
		return nil
	}
	if (data[0] == 0 && data[1]&0x80 == 0) || (data[0] == 0xff && data[1]&0x80 == 0x80) {
		return asn1.StructuralError{"integer not minimally-encoded"}
	}
	return nil
}

// parseInt64 treats the given bytes as a big-endian, signed integer and
// returns the result.
func parseInt64(data []byte) (ret int64, err error) {
	err = checkInteger(data)
	if err != nil {
		return
	}
	if len(data) > 8 {
		// We'll overflow an int64 in this case.
		err = asn1.StructuralError{"integer too large"}
		return
	}
	for bytesRead := 0; bytesRead < len(data); bytesRead++ {
		ret <<= 8
		ret |= int64(data[bytesRead])
	}

	// Shift up and down in order to sign extend the result.
	ret <<= 64 - uint8(len(data))*8
	ret >>= 64 - uint8(len(data))*8
	return
}

// parseInt treats the given bytes as a big-endian, signed integer and returns
// the result.
func parseInt32(data []byte) (int32, error) {
	if err := checkInteger(data); err != nil {
		return 0, err
	}
	ret64, err := parseInt64(data)
	if err != nil {
		return 0, err
	}
	if ret64 != int64(int32(ret64)) {
		return 0, asn1.StructuralError{"integer too large"}
	}
	return int32(ret64), nil
}

var bigOne = big.NewInt(1)

// parseBigInt treats the given bytes as a big-endian, signed integer and returns
// the result.
func parseBigInt(data []byte) (*big.Int, error) {
	if err := checkInteger(data); err != nil {
		return nil, err
	}
	ret := new(big.Int)
	if len(data) > 0 && data[0]&0x80 == 0x80 {
		// This is a negative number.
		notBytes := make([]byte, len(data))
		for i := range notBytes {
			notBytes[i] = ^data[i]
		}
		ret.SetBytes(notBytes)
		ret.Add(ret, bigOne)
		ret.Neg(ret)
		return ret, nil
	}
	ret.SetBytes(data)
	return ret, nil
}

// parseBitString parses an ASN.1 bit string from the given byte slice and returns it.
func parseBitString(data []byte) (ret asn1.BitString, err error) {
	if len(data) == 0 {
		err = asn1.SyntaxError{"zero length BIT STRING"}
		return
	}
	paddingBits := int(data[0])
	if paddingBits > 7 ||
		len(data) == 1 && paddingBits > 0 ||
		data[len(data)-1]&((1<<data[0])-1) != 0 {
		err = asn1.SyntaxError{"invalid padding bits in BIT STRING"}
		return
	}
	ret.BitLength = (len(data)-1)*8 - paddingBits
	ret.Bytes = data[1:]
	return
}

// parseObjectIdentifier parses an OBJECT IDENTIFIER from the given bytes and
// returns it. An object identifier is a sequence of variable length integers
// that are assigned in a hierarchy.
func parseObjectIdentifier(r io.ByteReader) (s []int, err error) {
	// The first varint is 40*value1 + value2:
	// According to this packing, value1 can take the values 0, 1 and 2 only.
	// When value1 = 0 or value1 = 1, then value2 is <= 39. When value1 = 2,
	// then there are no restrictions on value2.
	v, err := parseBase128Int(r)
	if err == io.EOF {
		err = asn1.SyntaxError{"zero length OBJECT IDENTIFIER"}
		return
	}

	s = make([]int, 2, 8)
	if v < 80 {
		s[0] = v / 40
		s[1] = v % 40
	} else {
		s[0] = 2
		s[1] = v - 80
	}

	for err == nil {
		v, err = parseBase128Int(r)
		if err == io.EOF {
		} else if err != nil {
			return
		} else {
			if len(s) == cap(s) {
				cpy := make([]int, cap(s)*2, len(s))
				copy(cpy, s)
				s = cpy
			}
			s = append(s, v)
		}
	}

	if err == io.EOF {
		err = nil
	}
	return
}

// parseBase128Int parses a base-128 encoded int from the given byte reader.
func parseBase128Int(r io.ByteReader) (ret int, err error) {
	var b byte
	for shifted := 0; err == nil; shifted++ {
		if shifted == 4 {
			err = asn1.StructuralError{"base 128 integer too large"}
			return
		}
		ret <<= 7
		b, err = r.ReadByte()
		if err != nil {
			return
		}
		ret |= int(b & 0x7f)
		if b&0x80 == 0 {
			return
		}
	}
	err = asn1.SyntaxError{"truncated base 128 integer"}
	return
}

// UTCTime

func parseUTCTime(data []byte) (ret time.Time, err error) {
	s := string(data)

	formatStr := "0601021504Z0700"
	ret, err = time.Parse(formatStr, s)
	if err != nil {
		formatStr = "060102150405Z0700"
		ret, err = time.Parse(formatStr, s)
	}
	if err != nil {
		return
	}

	if serialized := ret.Format(formatStr); serialized != s {
		err = fmt.Errorf("asn1: time did not serialize back to the original value and may be invalid: given %q, but serialized as %q", s, serialized)
		return
	}

	if ret.Year() >= 2050 {
		// UTCTime only encodes times prior to 2050. See https://tools.ietf.org/html/rfc5280#section-4.1.2.5.1
		ret = ret.AddDate(-100, 0, 0)
	}

	return
}

// parseGeneralizedTime parses the GeneralizedTime from the given byte slice
// and returns the resulting time.
func parseGeneralizedTime(data []byte) (ret time.Time, err error) {
	const formatStr = "20060102150405Z0700"
	s := string(data)

	if ret, err = time.Parse(formatStr, s); err != nil {
		return
	}

	if serialized := ret.Format(formatStr); serialized != s {
		err = fmt.Errorf("asn1: time did not serialize back to the original value and may be invalid: given %q, but serialized as %q", s, serialized)
	}

	return
}

// PrintableString

// parsePrintableString parses a ASN.1 PrintableString from the given byte
// array and returns it.
func parsePrintableString(data []byte) (ret string, err error) {
	for _, b := range data {
		if !isPrintable(b) {
			err = asn1.SyntaxError{"PrintableString contains invalid character"}
			return
		}
	}
	ret = string(data)
	return
}

// isPrintable reports whether the given b is in the ASN.1 PrintableString set.
func isPrintable(b byte) bool {
	return 'a' <= b && b <= 'z' ||
		'A' <= b && b <= 'Z' ||
		'0' <= b && b <= '9' ||
		'\'' <= b && b <= ')' ||
		'+' <= b && b <= '/' ||
		b == ' ' ||
		b == ':' ||
		b == '=' ||
		b == '?' ||
		// This is technically not allowed in a PrintableString.
		// However, x509 certificates with wildcard strings don't
		// always use the correct string type so we permit it.
		b == '*'
}

// IA5String

// parseIA5String parses a ASN.1 IA5String (ASCII string) from the given
// byte slice and returns it.
func parseIA5String(data []byte) (ret string, err error) {
	for _, b := range data {
		if b >= 0x80 {
			err = asn1.SyntaxError{"IA5String contains invalid character"}
			return
		}
	}
	ret = string(data)
	return
}

// T61String

// parseT61String parses a ASN.1 T61String (8-bit clean string) from the given
// byte slice and returns it.
func parseT61String(data []byte) (ret string, err error) {
	return string(data), nil
}

// UTF8String

// parseUTF8String parses a ASN.1 UTF8String (raw UTF-8) from the given byte
// array and returns it.
func parseUTF8String(data []byte) (ret string, err error) {
	if !utf8.Valid(data) {
		return "", errors.New("asn1: invalid UTF-8 string")
	}
	return string(data), nil
}

// Tagging

// parseTagAndLength parses an ASN.1 tag and length pair from the given byte
// reader into a byte slice. SET and SET OF (tag 17) are mapped to SEQUENCE and
// SEQUENCE OF (tag 16) since we don't distinguish between ordered and
// unordered objects in this code.
func parseTagAndLength(r io.ByteReader) (ret tagAndLength, err error) {
	var b byte
	b, err = r.ReadByte()
	// parseTagAndLength should not be called without at least a single
	// byte to read. Thus this check is for robustness:
	if err == io.EOF {
		err = errors.New("asn1: internal error in parseTagAndLength")
		return
	} else if err != nil {
		return
	}
	ret.class = int(b >> 6)
	ret.isCompound = b&0x20 == 0x20
	ret.tag = int(b & 0x1f)

	// If the bottom five bits are set, then the tag number is actually base 128
	// encoded afterwards
	if ret.tag == 0x1f {
		ret.tag, err = parseBase128Int(r)
		if err != nil {
			return
		}
	}
	b, err = r.ReadByte()
	if err == io.EOF {
		err = asn1.SyntaxError{"truncated tag or length"}
		return
	} else if err != nil {
		return
	}
	if b&0x80 == 0 {
		// The length is encoded in the bottom 7 bits.
		ret.length = int(b & 0x7f)
	} else {
		// Bottom 7 bits give the number of length bytes to follow.
		numBytes := int(b & 0x7f)
		if numBytes == 0 {
			err = asn1.SyntaxError{"indefinite length found (not DER)"}
			return
		}
		ret.length = 0
		for i := 0; i < numBytes; i++ {
			b, err = r.ReadByte()
			if err == io.EOF {
				err = asn1.SyntaxError{"truncated tag or length"}
				return
			} else if err != nil {
				return
			}
			if ret.length >= 1<<23 {
				// We can't shift ret.length up without
				// overflowing.
				err = asn1.StructuralError{"length too large"}
				return
			}
			ret.length <<= 8
			ret.length |= int(b)
			if ret.length == 0 {
				// DER requires that lengths be minimal.
				err = asn1.StructuralError{"superfluous leading zeros in length"}
				return
			}
		}
		// Short lengths must be encoded in short form.
		if ret.length < 0x80 {
			err = asn1.StructuralError{"non-minimal length"}
			return
		}
	}

	return
}

// parseSequenceOf is used for SEQUENCE OF and SET OF values. It tries to parse
// a number of ASN.1 values from the given byte slice and returns them as a
// slice of Go values of the given type.
func parseSequenceOf(r *bytes.Buffer, sliceType reflect.Type, elemType reflect.Type) (ret reflect.Value, err error) {
	params := fieldParameters{}
	ret = reflect.MakeSlice(sliceType, 8, 8)
	i := 0
	for ; r.Len() > 0; i++ {
		if i == ret.Len() {
			extra := reflect.MakeSlice(sliceType, 0, i*2)
			ret = reflect.AppendSlice(extra, ret)
		}
		_, err = parseField(ret.Index(i), r, params)
	}
	ret = ret.Slice(0, i)
	return
}

var (
	bitStringType        = reflect.TypeOf(asn1.BitString{})
	objectIdentifierType = reflect.TypeOf(asn1.ObjectIdentifier{})
	enumeratedType       = reflect.TypeOf(asn1.Enumerated(0))
	flagType             = reflect.TypeOf(asn1.Flag(false))
	timeType             = reflect.TypeOf(time.Time{})
	rawValueType         = reflect.TypeOf(asn1.RawValue{})
	rawContentsType      = reflect.TypeOf(asn1.RawContent(nil))
	bigIntType           = reflect.TypeOf(new(big.Int))
)

// invalidLength returns true iff offset + length > sliceLength, or if the
// addition would overflow.
func invalidLength(offset, length, sliceLength int) bool {
	return offset+length < offset || offset+length > sliceLength
}

// parseField is the main parsing function. Given a byte slice and an offset
// into the array, it will try to parse a suitable ASN.1 value out and store it
// in the given Value.
func parseField(v reflect.Value, r *bytes.Buffer, params fieldParameters) (offset int, err error) {
	// If we have run out of data, it may be that there are optional elements at the end.

	dataSize := r.Len()
	if dataSize == 0 {
		if !setDefaultValue(v, params) {
			err = asn1.SyntaxError{"sequence truncated"}
		}
		return
	}
	data := r.Bytes()
	t, err := parseTagAndLength(r)
	if err == nil && r.Len() < t.length {
		err = asn1.SyntaxError{"data truncated"}
	}
	if err != nil {
		return
	}
	offset = dataSize - r.Len() + t.length

	// Deal with raw values.
	fieldType := v.Type()
	if fieldType == rawValueType {
		result := asn1.RawValue{t.class, t.tag, t.isCompound, r.Next(t.length), data[:offset]}
		v.Set(reflect.ValueOf(result))
		return
	}

	// Deal with the ANY type.
	if ifaceType := fieldType; ifaceType.Kind() == reflect.Interface && ifaceType.NumMethod() == 0 {
		var result interface{}
		if !t.isCompound && t.class == asn1.ClassUniversal {
			innerBytes := r.Next(t.length)
			inner := bytes.NewReader(innerBytes)
			switch t.tag {
			case asn1.TagPrintableString:
				result, err = parsePrintableString(innerBytes)
			case asn1.TagIA5String:
				result, err = parseIA5String(innerBytes)
			case asn1.TagT61String:
				result, err = parseT61String(innerBytes)
			case asn1.TagUTF8String:
				result, err = parseUTF8String(innerBytes)
			case asn1.TagInteger:
				result, err = parseInt64(innerBytes)
			case asn1.TagBitString:
				result, err = parseBitString(innerBytes)
			case asn1.TagOID:
				result, err = parseObjectIdentifier(inner)
			case asn1.TagUTCTime:
				result, err = parseUTCTime(innerBytes)
			case asn1.TagGeneralizedTime:
				result, err = parseGeneralizedTime(innerBytes)
			case asn1.TagOctetString:
				result = innerBytes
			default:
				// If we don't know how to handle the type, we just leave Value as nil.
			}
		}
		if err == nil && result != nil {
			v.Set(reflect.ValueOf(result))
		}
		return
	}
	universalTag, compoundType, ok1 := getUniversalType(fieldType)
	if !ok1 {
		err = asn1.StructuralError{fmt.Sprintf("unknown Go type: %v", fieldType)}
		return
	}

	if params.explicit {
		expectedClass := asn1.ClassContextSpecific
		if params.application {
			expectedClass = asn1.ClassApplication
		}
		if r.Len() == 0 {
			err = asn1.StructuralError{"explicit tag has no child"}
			return
		}
		if t.class == expectedClass && t.tag == *params.tag && (t.length == 0 || t.isCompound) {
			if t.length > 0 {
				if r.Len() == 0 {
					err = asn1.SyntaxError{"data truncated"}
					return
				}
				t, err = parseTagAndLength(r)
				if err != nil {
					return
				}
				offset = dataSize - r.Len()
			} else {
				if fieldType != flagType {
					err = asn1.StructuralError{"zero length explicit tag was not an asn1.asn1.Flag"}
					return
				}
				v.SetBool(true)
				return
			}
		} else {
			// The tags didn't match, it might be an optional element.
			ok := setDefaultValue(v, params)
			if ok {
				offset = 0
			} else {
				err = asn1.StructuralError{"explicitly tagged member didn't match"}
			}
			return
		}
	}

	// Special case for strings: all the ASN.1 string types map to the Go
	// type string. getUniversalType returns the tag for PrintableString
	// when it sees a string, so if we see a different string type on the
	// wire, we change the universal type to match.
	if universalTag == asn1.TagPrintableString {
		if t.class == asn1.ClassUniversal {
			switch t.tag {
			case asn1.TagIA5String, asn1.TagGeneralString, asn1.TagT61String, asn1.TagUTF8String:
				universalTag = t.tag
			}
		} else if params.stringType != 0 {
			universalTag = params.stringType
		}
	}

	// Special case for time: UTCTime and GeneralizedTime both map to the
	// Go type time.Time.
	if universalTag == asn1.TagUTCTime && t.tag == asn1.TagGeneralizedTime && t.class == asn1.ClassUniversal {
		universalTag = asn1.TagGeneralizedTime
	}

	if params.set {
		universalTag = asn1.TagSet
	}

	expectedClass := asn1.ClassUniversal
	expectedTag := universalTag

	if !params.explicit && params.tag != nil {
		expectedClass = asn1.ClassContextSpecific
		expectedTag = *params.tag
	}

	if !params.explicit && params.application && params.tag != nil {
		expectedClass = asn1.ClassApplication
		expectedTag = *params.tag
	}

	// We have unwrapped any explicit tagging at this point.
	if t.class != expectedClass || t.tag != expectedTag || t.isCompound != compoundType {
		// Tags don't match. Again, it could be an optional element.
		ok := setDefaultValue(v, params)
		if ok {
			offset = 0
		} else {
			err = asn1.StructuralError{fmt.Sprintf("tags don't match (%d vs %+v) %+v %s @%d", expectedTag, t, params, fieldType.Name(), offset)}
		}
		return
	}
	if r.Len() < t.length {
		err = asn1.SyntaxError{"data truncated"}
		return
	}
	innerBytes := r.Next(t.length)
	offset = dataSize - r.Len()
	inner := bytes.NewBuffer(innerBytes)

	// We deal with the structures defined in this package first.
	switch fieldType {
	case objectIdentifierType:
		newSlice, err1 := parseObjectIdentifier(inner)
		v.Set(reflect.MakeSlice(v.Type(), len(newSlice), len(newSlice)))
		if err1 == nil {
			reflect.Copy(v, reflect.ValueOf(newSlice))
		}
		err = err1
		return
	case bitStringType:
		bs, err1 := parseBitString(innerBytes)
		if err1 == nil {
			v.Set(reflect.ValueOf(bs))
		}
		err = err1
		return
	case timeType:
		var time time.Time
		var err1 error
		if universalTag == asn1.TagUTCTime {
			time, err1 = parseUTCTime(innerBytes)
		} else {
			time, err1 = parseGeneralizedTime(innerBytes)
		}
		if err1 == nil {
			v.Set(reflect.ValueOf(time))
		}
		err = err1
		return
	case enumeratedType:
		parsedInt, err1 := parseInt32(innerBytes)
		if err1 == nil {
			v.SetInt(int64(parsedInt))
		}
		err = err1
		return
	case flagType:
		v.SetBool(true)
		return
	case bigIntType:
		parsedInt, err1 := parseBigInt(innerBytes)
		if err1 == nil {
			v.Set(reflect.ValueOf(parsedInt))
		}
		err = err1
		return
	}
	switch val := v; val.Kind() {
	case reflect.Bool:
		parsedBool, err1 := parseBool(innerBytes)
		if err1 == nil {
			val.SetBool(parsedBool)
		}
		err = err1
		return
	case reflect.Int, reflect.Int32, reflect.Int64:
		if val.Type().Size() == 4 {
			parsedInt, err1 := parseInt32(innerBytes)
			if err1 == nil {
				val.SetInt(int64(parsedInt))
			}
			err = err1
		} else {
			parsedInt, err1 := parseInt64(innerBytes)
			if err1 == nil {
				val.SetInt(parsedInt)
			}
			err = err1
		}
		return
	// TODO(dfc) Add support for the remaining integer types
	case reflect.Struct:
		structType := fieldType

		if structType.NumField() > 0 &&
			structType.Field(0).Type == rawContentsType {
			dataBytes := data[:offset]
			val.Field(0).Set(reflect.ValueOf(asn1.RawContent(dataBytes)))
		}

		innerOffset := 0
		for i := 0; i < structType.NumField(); i++ {
			field := structType.Field(i)
			if i == 0 && field.Type == rawContentsType {
				continue
			}
			n := 0
			inner := bytes.NewBuffer(innerBytes[innerOffset:])
			n, err = parseField(val.Field(i), inner, parseFieldParameters(field.Tag.Get("asn1")))
			innerOffset += n
			if err != nil {
				return
			}
		}
		// We allow extra bytes at the end of the SEQUENCE because
		// adding elements to the end has been used in X.509 as the
		// version numbers have increased.
		return
	case reflect.Slice:
		sliceType := fieldType
		if sliceType.Elem().Kind() == reflect.Uint8 {
			val.Set(reflect.MakeSlice(sliceType, len(innerBytes), len(innerBytes)))
			reflect.Copy(val, reflect.ValueOf(innerBytes))
			return
		}
		newSlice, err1 := parseSequenceOf(inner, sliceType, sliceType.Elem())
		if err1 == nil {
			val.Set(newSlice)
		}
		err = err1
		return
	case reflect.String:
		var v string
		switch universalTag {
		case asn1.TagPrintableString:
			v, err = parsePrintableString(innerBytes)
		case asn1.TagIA5String:
			v, err = parseIA5String(innerBytes)
		case asn1.TagT61String:
			v, err = parseT61String(innerBytes)
		case asn1.TagUTF8String:
			v, err = parseUTF8String(innerBytes)
		case asn1.TagGeneralString:
			// GeneralString is specified in ISO-2022/ECMA-35,
			// A brief review suggests that it includes structures
			// that allow the encoding to change midstring and
			// such. We give up and pass it as an 8-bit string.
			v, err = parseT61String(innerBytes)
		default:
			err = asn1.SyntaxError{fmt.Sprintf("internal error: unknown string type %d", universalTag)}
		}
		if err == nil {
			val.SetString(v)
		}
		return
	}
	err = asn1.StructuralError{"unsupported: " + v.Type().String()}
	return
}

// canHaveDefaultValue reports whether k is a Kind that we will set a default
// value for. (A signed integer, essentially.)
func canHaveDefaultValue(k reflect.Kind) bool {
	switch k {
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return true
	}

	return false
}

// setDefaultValue is used to install a default value, from a tag string, into
// a Value. It is successful if the field was optional, even if a default value
// wasn't provided or it failed to install it into the Value.
func setDefaultValue(v reflect.Value, params fieldParameters) (ok bool) {
	if !params.optional {
		return
	}
	ok = true
	if params.defaultValue == nil {
		return
	}
	if canHaveDefaultValue(v.Kind()) {
		v.SetInt(*params.defaultValue)
	}
	return
}

// Unmarshal parses the DER-encoded ASN.1 data structure b
// and uses the reflect package to fill in an arbitrary value pointed at by val.
// Because Unmarshal uses the reflect package, the structs
// being written to must use upper case field names.
//
// An ASN.1 INTEGER can be written to an int, int32, int64,
// or *big.Int (from the math/big package).
// If the encoded value does not fit in the Go type,
// Unmarshal returns a parse error.
//
// An ASN.1 BIT STRING can be written to a asn1.BitString.
//
// An ASN.1 OCTET STRING can be written to a []byte.
//
// An ASN.1 OBJECT IDENTIFIER can be written to an
// asn1.ObjectIdentifier.
//
// An ASN.1 ENUMERATED can be written to an asn1.Enumerated.
//
// An ASN.1 UTCTIME or GENERALIZEDTIME can be written to a time.Time.
//
// An ASN.1 PrintableString or IA5String can be written to a string.
//
// Any of the above ASN.1 values can be written to an interface{}.
// The value stored in the interface has the corresponding Go type.
// For integers, that type is int64.
//
// An ASN.1 SEQUENCE OF x or SET OF x can be written
// to a slice if an x can be written to the slice's element type.
//
// An ASN.1 SEQUENCE or SET can be written to a struct
// if each of the elements in the sequence can be
// written to the corresponding element in the struct.
//
// The following tags on struct fields have special meaning to Unmarshal:
//
//	application	specifies that a APPLICATION tag is used
//	default:x	sets the default value for optional integer fields
//	explicit	specifies that an additional, explicit tag wraps the implicit one
//	optional	marks the field as ASN.1 OPTIONAL
//	set		causes a SET, rather than a SEQUENCE type to be expected
//	tag:x		specifies the ASN.1 tag number; implies ASN.1 CONTEXT SPECIFIC
//
// If the type of the first field of a structure is asn1.RawContent then the raw
// ASN1 contents of the struct will be stored in it.
//
// If the type name of a slice element ends with "SET" then it's treated as if
// the "set" tag was set on it. This can be used with nested slices where a
// struct tag cannot be given.
//
// Other ASN.1 types are not supported; if it encounters them,
// Unmarshal returns a parse error.
func Unmarshal(b []byte, val interface{}) (rest []byte, err error) {
	v := reflect.ValueOf(val).Elem()
	r := bytes.NewBuffer(b)
	_, err = parseField(v, r, parseFieldParameters(""))
	if err == nil {
		rest = r.Bytes()
	}
	return
}
