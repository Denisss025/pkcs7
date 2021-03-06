package pkcs7

import (
	"bytes"
	"encoding/asn1"
	"strings"
	"testing"
)

func TestBer2Der(t *testing.T) {
	// indefinite length fixture
	ber := []byte{0x30, 0x80, 0x02, 0x01, 0x01, 0x00, 0x00}
	expected := []byte{0x30, 0x03, 0x02, 0x01, 0x01}
	buf := &bytes.Buffer{}

	if err := ber2der(buf, bytes.NewReader(ber)); err != nil {
		t.Fatalf("ber2der failed with error: %v", err)
	}
	if bytes.Compare(buf.Bytes(), expected) != 0 {
		t.Errorf("ber2der result did not match.\n\tExpected: % X\n\tActual: % X", expected, buf.Bytes())
	}

	buf2 := &bytes.Buffer{}
	if err := ber2der(buf2, bytes.NewReader(buf.Bytes())); err != nil {
		t.Errorf("ber2der on DER bytes failed with error: %v", err)
	} else {
		if !bytes.Equal(buf.Bytes(), buf2.Bytes()) {
			t.Error("ber2der is not idempotent")
		}
	}
	var thing struct {
		Number int
	}
	rest, err := asn1.Unmarshal(buf.Bytes(), &thing)
	if err != nil {
		t.Errorf("Cannot parse resulting DER because: %v", err)
	} else if len(rest) > 0 {
		t.Errorf("Resulting DER has trailing data: % X", rest)
	}
}

func TestBer2Der_Negatives(t *testing.T) {
	fixtures := []struct {
		Input         []byte
		ErrorContains string
	}{
		{[]byte{0x30, 0x85}, "length too long"},
		{[]byte{0x30, 0x84, 0x80, 0x0, 0x0, 0x0}, "length is negative"},
		{[]byte{0x30, 0x82, 0x0, 0x1}, "length has leading zero"},
		{[]byte{0x30, 0x80, 0x1, 0x2}, "Invalid BER format"},
		{[]byte{0x30, 0x03, 0x01, 0x02}, "length is more than available data"},
	}

	buf := &bytes.Buffer{}
	for _, fixture := range fixtures {
		buf.Reset()
		err := ber2der(buf, bytes.NewReader(fixture.Input))
		if err == nil {
			t.Errorf("No error thrown. Expected: %s", fixture.ErrorContains)
		}
		if !strings.Contains(err.Error(), fixture.ErrorContains) {
			t.Errorf("Unexpected error thrown.\n\tExpected: /%s/\n\tActual: %s", fixture.ErrorContains, err.Error())
		}
	}
}
