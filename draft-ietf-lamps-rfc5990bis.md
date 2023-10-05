---
title: Use of the RSA-KEM Algorithm in the Cryptographic Message Syntax (CMS)
abbrev: RSA-KEM with CMS KEMRecipientInfo
category: std
docname: draft-ietf-lamps-rfc5990bis-latest
submissiontype: IETF
obsoletes: 5990
ipr: trust200902
date:
consensus: true
pi:
  toc: 'yes'
  sortrefs: 'yes'
  symrefs: 'yes'
area: "Security"
workgroup: "Limited Additional Mechanisms for PKIX and SMIME"
keyword:
 - Key Encapsulation Mechanism (KEM)
 - KEMRecipientInfo
venue:
  group: "Limited Additional Mechanisms for PKIX and SMIME"
  type: "Working Group"
  mail: "spasm@ietf.org"
  arch: "https://mailarchive.ietf.org/arch/browse/spasm/"

author:
 -
    name: Russ Housley
    org: Vigil Security, LLC
    abbrev: Vigil Security
    street: 516 Dranesville Road
    city: Herndon, VA
    code: 20170
    country: US
    email: housley@vigilsec.com
 -
    name: Sean Turner
    ins: S. Turner
    organization: sn3rd
    email: sean@sn3rd.com

normative:
  I-D.ietf-lamps-cms-kemri:
  RFC5083:
  RFC5280:
  RFC5652:
  RFC5911:
  RFC5912:
  RFC6268:
  RFC8551:
  SHS:
    author:
      org: National Institute of Standards and Technology
    title: "Secure Hash Standard"
    date: 2015-07
    seriesinfo:
      "NIST": "FIPS 180-4"
    seriesinfo:
      DOI: 10.6028/nist.fips.180-4
  X.680:
    target: https://www.itu.int/rec/T-REC-X.680
    title: >
      Information technology --
      Abstract Syntax Notation One (ASN.1):
      Specification of basic notation
    author:
    - org: ITU-T
    date: 2021-02
    seriesinfo:
      ITU-T Recommendation: X.680
      ISO/IEC: 8824-1:2021
  X.690:
    target: https://www.itu.int/rec/T-REC-X.680
    title: >
      Information technology --
      ASN.1 encoding rules: Specification of Basic Encoding Rules (BER),
      Canonical Encoding Rules (CER) and Distinguished Encoding Rules (DER)
    author:
    - org: ITU-T
    date: 2021-02
    seriesinfo:
      ITU-T Recommendation: X.690
      ISO/IEC: 8825-1:2021
  ISO18033-2:
    target: https://www.iso.org/standard/37971.html
    title: >
      Information technology --
      Security techniques --
      Encryption algorithms --
      Part 2: Asymmetric ciphers
    author:
    - org:  ISO/IEC JTC 1/SC 27
    date: 2006
    seriesinfo:
      ISO/IEC: 18033-2:2006

informative:
  RFC3394:
  RFC4086:
  RFC5990:
  RFC6194:
  RFC8017:
  NISTSP800-57pt1r5:
    author:
      org: National Institute of Standards and Technology
    title: "Recommendation for Key Management:Part 1 - General"
    date: 2020-05
    seriesinfo:
      "NIST": "Special Publication 800-57 Part 1 Revision 5"
    seriesinfo:
      DOI: 10.6028/nist.sp.800-57pt1r5
  ANS-X9.44:
   author:
     org: American National Standards Institute
   title: >
     Public Key Cryptography for the Financial Services Industry --
     Key Establishment Using Integer Factorization Cryptography
   date: 2007
   seriesinfo:
     American National Standard: X9.44
  CMVP:
    target: https://csrc.nist.gov/projects/cryptographic-module-validation-program
    author:
      org: National Institute of Standards and Technology
    title: "Cryptographic Module Validation Program"
    date: 2016
  SHOUP:
    target: https://eprint.iacr.org/2001/112
    author:
      name: Victor Shoup
      ins: V. Shoup
    title: A Proposal for an ISO Standard for Public Key Encryption
    date: 2001
    seriesinfo:
      Cryptology ePrint Archive: Paper 2001/112

--- abstract

The RSA Key Encapsulation Mechanism (RSA-KEM) Algorithm is a one-pass
(store-and-forward) cryptographic mechanism for an originator to securely
send keying material to a recipient using the recipient's RSA public key.
The RSA-KEM Algorithm is specified in Clause 11.5 of ISO/IEC: 18033-2:2006.
This document specifies the conventions for using the RSA-KEM Algorithm
either as a standalone KEM algorithm or with the Cryptographic Message
Syntax (CMS) using KEMRecipientInfo as specified in draft-ietf-lamps-cms-kemri.

--- middle

# Introduction

The RSA Key Encapsulation Mechanism (RSA-KEM) Algorithm is a one-pass
(store-and-forward) cryptographic mechanism for an originator to securely
send keying material to a recipient using the recipient's RSA public key.
The RSA-KEM Algorithm is specified in Clause 11.5 of {{ISO18033-2}}.

The RSA-KEM Algorithm takes a different approach than other RSA key
transport mechanisms {{RFC8017}}, with the goal of first, providing higher
security assurance, and second satisfying the KEM interface as described
in {{app-alg}} instead of the Key Transport interface as is traditionally
done with RSA-based mechanisms.  The RSA-KEM Algorithm encrypts a random
integer with the recipient's RSA public key, and derives a shared secret
from the random integer which can be directly used by the originator
and recipient as a symmetric key for example to wrap a content encryption
key.


1. Generate a random integer z between 0 and n-1.

2. Encrypt the integer z with the recipient's RSA public key:

   ~~~
       c = z^e mod n
   ~~~

3. Derive a shared secret SS from the integer z:

   ~~~
       SS = KDF(z)
   ~~~

4. Return the ciphertext C and the shared secret SS.



In the original RSA-KEM as published in [RFC5990], the RSA-KEM algorithm
needed to achieve compatibility with CMS KeyTransRecipientInfo which it
did by including an additional step to wrap a symmetric content-encryption
key with the shared secret acting as a Key-encrypting-key (KEK).  In this
way, the originator and the recipient end up with the same
content-encryption-key (CEK).   Given a
content-encryption key CEK, the original RSA-KEM can be summarized as:


4. Wrap the CEK with the KEK to obtain wrapped keying material WK:

   ~~~
       WK = WRAP(KEK, CEK)
   ~~~

5. The originator sends c and WK to the recipient.

This KEM-based approach provides higher security assurance for two
reasons.  First, the input to the underlying RSA operation is effectively
a random integer between 0 and n-1, where n is the RSA modulus, so it does
not have any structure that could be exploited by an adversary.  Second,
the input is independent of the keying material so the result of the
RSA decryption operation is not directly available to an adversary.
As a result, the RSA-KEM Algorithm enjoys a "tight" security proof in the
random oracle model.  (In other padding schemes, such as
PKCS #1 v1.5 {{RFC8017}}, the input has structure and/or depends on the
keying material, and the provable security assurances are not as
strong.)  The approach is also architecturally convenient because the
public-key operations are separate from the symmetric operations on the
keying material.  Another benefit is that the length of the keying material
is bounded only by the symmetric key-wrapping algorithm, not the size of
the RSA modulus.

For completeness, a specification of the RSA-KEM Algorithm is given in
Appendix A of this document; ASN.1 syntax is given in Appendix B.

## Conventions and Definitions

{::boilerplate bcp14-tagged}

## ASN.1

CMS values are generated using ASN.1 {{X.680}}, which uses the Basic
Encoding Rules (BER) and the Distinguished Encoding Rules (DER) {{X.690}}.

## Changes Since RFC 5990

RFC 5990 {{RFC5990}} specified the conventions for using the RSA-KEM Algorithm
in CMS as a key transport algorithm.  That is, it used KeyTransRecipientInfo {{RFC5652}}
for each recipient.  This approach resulted in a very complex parameter
definition with the id-rsa-kem algorithm identifier.  Implementation
experience with many different algorithms has shown that complex
parameter structures cause interoperability issues.  Since the publication
of RFC 5990, a new KEMRecipientInfo structure {{I-D.ietf-lamps-cms-kemri}}
has been defined to support KEM algorithms, and this new structure avoids the
complex parameters structure that was used in RFC 5990.  Likewise, when
the id-rsa-kem algorithm identifier appears in the SubjectPublicKeyInfo
field of a certificate, this document encourages the omission of any
parameters.  Also, to avoid visual confusion with id-kem-rsa, id-rsa-kem-spki
is introduced as an alias for id-rsa-kem.

RFC 5990 uses EK and the EncryptedKey, which is the concatenation of
C and WK (C || WK).  The use of EK is necessary to align with the
KeyTransRecipientInfo structure.  In this document, C and WK are sent
in separate fields of new KEMRecipientInfo structure.  In particular,
C is carried in the kemct field, and WK is carried in the encryptedKey
field.

RFC 5990 supports the future definition of additional KEM algorithms that
use RSA; this document supports only one, and it is identified by the
id-kem-rsa object identifier.

RFC 5990 includes support for Camellia and Triple-DES block ciphers;
discussion of these block ciphers is removed from this document, but
the algorithm identifiers remain in the ASN.1 Module {{app-asn1-module}}.

RFC 5990 includes support for SHA-1 hash function; discussion of this
hash function is removed from this document, but the algorithm identifier
remains in the ASN.1 module {{app-asn1-module}}.

RFC 5990 required support for the KDF3 {{ANS-X9.44}} key-derivation
function; this document continues to require support for the KDF3
key-derivation function, but it requires support for SHA-256 {{SHS}} as
the hash function.

RFC 5990 recommends support for alternatives to KDF3 and AES-Wrap-128;
this document simply states that other key-derivation functions and
key-encryption algorithms MAY be supported.

RFC 5990 includes an ASN.1 module; this document provides an alternative
ASN.1 module that follows the conventions established in {{RFC5911}},
{{RFC5912}}, and {{RFC6268}}. The new ASN.1 module {{app-asn1-module}}
produces the same bits-on-the-wire as the one in RFC 5990.

# Use of the RSA-KEM Algorithm in CMS

The RSA-KEM Algorithm MAY be employed for one or more recipients in the
CMS enveloped-data content type {{RFC5652}}, the CMS authenticated-data
content type {{RFC5652}}, or the CMS authenticated-enveloped-data
content type {{RFC5083}}.  In each case, the KEMRecipientInfo
{{I-D.ietf-lamps-cms-kemri}} is used with with the RSA-KEM Algorithm
to securely transfer the content-encryption key from the originator to
the recipient.

## Underlying Components

A CMS implementation that supports the RSA-KEM Algorithm MUST support at
least the following underlying components:

- For the key-derivation function, an implementation MUST support
  KDF3 {{ANS-X9.44}} with SHA-256 {{SHS}}.

- For key-wrapping, an implementation MUST support the
  AES-Wrap-128 {{RFC3394}} key-encryption algorithm.

An implementation MAY also support other key-derivation functions and
key-encryption algorithms as well.

## RecipientInfo Conventions

When the RSA-KEM Algorithm is employed for a recipient, the
RecipientInfo alternative for that recipient MUST be
OtherRecipientInfo using the KEMRecipientInfo structure
{{I-D.ietf-lamps-cms-kemri}}.  The fields of the
KEMRecipientInfo MUST have the following values:

> version is the syntax version number; it MUST be 0.

> rid identifies the recipient's certificate or public key.

> kem identifies the KEM algorithm; it MUST contain id-kem-rsa.

> kemct is the ciphertext produced for this recipient; it contains
C from steps 1 and 2 of Originator's Operations in {{app-alg}}.

> kdf identifies the key-derivation algorithm. Note that the KDF
> specified and used at the CMS RecipientInfo level does not need to be
> the same as the KDF used within the RSA-KEM construction as specified
> in {{app-alg}}.

> kekLength is the size of the key-encryption key in octets.

> ukm is an optional random input to the key-derivation function.

> wrap identifies a key-encryption algorithm used to encrypt the
content-encryption key.

> encryptedKey is the result of encrypting the keying material with the
key-encryption key.  When used with the CMS enveloped-data content
type {{RFC5652}}, the keying material is a content-encryption key.  When
used with the CMS authenticated-data content type {{RFC5652}}, the
keying material is a message-authentication key.  When used with the
CMS authenticated-enveloped-data content type {{RFC5083}}, the
keying material is a content-authenticated-encryption key.

NOTE: For backward compatibility, implementations MAY
also support RSA-KEM Key Transport Algorithm denoted by `id-rsa-kem`, which uses
KeyTransRecipientInfo as specified in {{RFC5990}}.


## Certificate Conventions

The conventions specified in this section augment RFC 5280 {{RFC5280}}.

A recipient who employs the RSA-KEM Algorithm MAY identify the public key
in a certificate by the same AlgorithmIdentifier as for the
PKCS #1 v1.5 algorithm, that is, using the rsaEncryption object
identifier {{RFC8017}}.  The fact that the recipient will accept RSA-KEM
with this public key is not indicated by the use of this object
identifier.  The willingness to accept the RSA-KEM Algorithm MAY be
signaled by the use of the appropriate SMIME Capabilities either in a
message or in the certificate.

If the recipient wishes only to employ the RSA-KEM Algorithm with a given
public key, the recipient MUST identify the public key in the certificate
using the id-rsa-kem-spki object identifier; see {{app-asn1}}.  When the
id-rsa-kem-spki object identifier appears in the SubjectPublicKeyInfo algorithm
field of the certificate, the parameters field from AlgorithmIdentifier
SHOULD be absent.  That is, the AlgorithmIdentifier SHOULD be a SEQUENCE of
one component, the id-rsa-kem-spki object identifier.

When the AlgorithmIdentifier parameters are present, the
GenericHybridParameters MUST be used.  As described in the next
section, the GenericHybridParameters constrain the values that can
be used with the RSA public key for the kdf, kekLength, and wrap
fields of the KEMRecipientInfo structure.

Regardless of the AlgorithmIdentifier used, the RSA public key MUST be
carried in the subjectPublicKey BIT STRING within the SubjectPublicKeyInfo
filed of the certificate using the RSAPublicKey type defined in {{RFC8017}}.

The intended application for the public key MAY be indicated in the key
usage certificate extension as specified in {{Section 4.2.1.3 of RFC5280}}.  If
the keyUsage extension is present in a certificate that conveys an RSA
public key with the id-rsa-kem-spki object identifier as discussed above,
then the key usage extension MUST contain the following value:

> keyEncipherment

The digitalSignatrure and dataEncipherment values SHOULD NOT be
present.  That is, a public key intended to be employed only with the
RSA-KEM Algorithm SHOULD NOT also be employed for data encryption or
for digital signatures.  Good cryptographic practice employs a given RSA
key pair in only one scheme.  This practice avoids the risk that vulnerability
in one scheme may compromise the security of the other, and may be
essential to maintain provable security.

## SMIMECapabilities Attribute Conventions

{{Section 2.5.2 of RFC8551}} defines the SMIMECapabilities signed
attribute (defined as a SEQUENCE of SMIMECapability SEQUENCEs) to
announce a partial list of algorithms that an S/MIME implementation
can support.  When constructing a CMS signed-data content type {{RFC5652}},
a compliant implementation MAY include the SMIMECapabilities signed
attribute announcing that it supports the RSA-KEM Algorithm.

The SMIMECapability SEQUENCE representing the RSA-KEM Algorithm MUST
include the id-rsa-kem-spki object identifier in the capabilityID field;
see {{app-asn1}} for the object identifier value, and see {{app-example}}
for examples.  When the id-rsa-kem-spki object identifier appears in the
capabilityID field and the parameters are present, then the parameters
field MUST use the GenericHybridParameters type.

~~~
  GenericHybridParameters ::= SEQUENCE {
    kem  KeyEncapsulationMechanism,
    dem  DataEncapsulationMechanism }
~~~

The fields of the GenericHybridParameters type have the following meanings:

> kem is an AlgorithmIdentifer; the algorithm field MUST be set to id-kem-rsa;
the parameters field MUST be RsaKemParameters, which is a SEQUENCE of an
AlgorithmIdentifier that identifies the supported key-derivation function
and a positive INTEGER that identifies the length of the key-encryption
key in octets.  If the GenericHybridParameters are present, then the
provided kem value MUST be used as the key-derivation function in the
kdf field of KEMRecipientInfo, and the provided key length MUST be used
in the kekLength of KEMRecipientInfo.

> dem is an AlgorithmIdentifier; the algorithm field MUST be present, and it
identifies the key-encryption algorithm; parameters are optional.  If the
GenericHybridParameters are present, then the provided dem value MUST be
used in the wrap field of KEMRecipientInfo.

# Security Considerations

The RSA-KEM Algorithm should be considered as a replacement for the
widely implemented PKCS #1 v1.5 {{RFC8017}} for new applications
that use CMS to avoid potential vulnerabilities to chosen-ciphertext
attacks and gain a tighter security proof; however, the RSA-KEM Algorithm
has the disadvantage of slightly longer encrypted keying material.

The security of the RSA-KEM Algorithm can be shown to be tightly related
to the difficulty of either solving the RSA problem or, in the case of the
original [RFC5990] algorithm, breaking the
underlying symmetric key-encryption algorithm, if the underlying
key-derivation function is modeled as a random oracle, and assuming that
the symmetric key-encryption algorithm satisfies the properties of a
data encapsulation mechanism {{SHOUP}}.  While in practice a random-oracle
result does not provide an actual security proof for any particular
key-derivation function, the result does provide assurance that the general
construction is reasonable; a key-derivation function would need to be
particularly weak to lead to an attack that is not possible in the
random-oracle model.

The RSA key size and the underlying components need to be selected
consistent with the desired security level.  Several security levels
have been identified in the NIST SP 800-57 Part 1 {{NISTSP800-57pt1r5}}.
To achieve 128-bit security, the RSA key size SHOULD be at least 3072 bits,
the key-derivation function SHOULD make use of SHA-256, and the symmetric
key-encryption algorithm SHOULD be AES Key Wrap with a 128-bit key.

Implementations MUST protect the RSA private key, the key-encryption key,
the content-encryption key, the content-authenticated-encryption key.
Compromise of the RSA private key could result in the disclosure of all
messages protected with that key.  Compromise of the key-encryption key,
the content-encryption key, or content-authenticated-encryption key could
result in disclosure of the associated encrypted content.

Additional considerations related to key management may be found in
{{NISTSP800-57pt1r5}}.

The RSA-KEM algorithm does not use an explicit padding scheme, but instead directly
encrypts the string representation of the integer Z.
There is implicit padding in that Z is to be chosen uniformly randomly
on the interval (0, n-1) where n is the modulus of the RSA public key
and that `IntegerToString(z, nLen)` should produce a string the full
length of the modulus. Implementors of originators MUST ensure that
these conditions are met. Implementors of recipients should consider
the impacts to protocol security if the originator is malicious
and z or Z are chosen maliciously. In most cases this will be protected
for by the act of hashing Z with KDF, and for this reason implentations
SHOULD NOT use z or Z directly for any purpose.

RSA-KEM provides both a fixed-length ciphertext -- which MUST be checked
by the recipient prior to a decryption attempt as per Step 1 in
{{app-alg-decaps}} -- and a fixed-length shared secret -- which is
guaranteed by the application of KDF in Step 4 in {{app-alg-decaps}}.

The security of the RSA-KEM Algorithm also depends on the strength of the
random number generator used by the originator to generate Z, which
SHOULD have a comparable security level.  For
further discussion on random number generation, see {{RFC4086}}.

Implementations SHOULD NOT reveal information about intermediate
values or calculations, whether by timing or other "side channels",
otherwise an opponent may be able to determine information about
the keying data and/or the recipient's private key.  Although not all
intermediate information may be useful to an opponent, it is
preferable to conceal as much information as is practical, unless
analysis specifically indicates that the information would not be
useful to an opponent.

Generally, good cryptographic practice employs a given RSA key pair
in only one scheme.  This practice avoids the risk that vulnerability
in one scheme may compromise the security of the other, and may be
essential to maintain provable security.  While RSA public keys have
often been employed for multiple purposes such as key transport and
digital signature without any known bad interactions, for increased
security assurance, such combined use of an RSA key pair is NOT
RECOMMENDED in the future (unless the different schemes are
specifically designed to be used together).

Accordingly, an RSA key pair used for the RSA-KEM Algorithm SHOULD NOT
also be used for digital signatures.  Indeed, the Accredited Standards
Committee X9 (ASC X9) requires such a separation between key pairs used
for key establishment and key pairs used for digital signature
{{ANS-X9.44}}.  Continuing this principle of key separation, a key pair
used for the RSA-KEM Algorithm SHOULD NOT be used with other key
establishment schemes, or for data encryption, or with more
than one set of underlying algorithm components.

Parties MAY gain assurance that implementations are correct through
formal implementation validation, such as the NIST Cryptographic
Module Validation Program (CMVP) {{CMVP}}.

# IANA Considerations

For the ASN.1 Module in {{app-asn1-module}}, IANA is requested to assign an
object identifier (OID) for the module identifier. The OID for the module
should be allocated in the "SMI Security for S/MIME Module Identifier"
registry (1.2.840.113549.1.9.16.0), and the Description for the new OID
should be set to "id-mod-cms-rsa-kem-2023".

--- back

# RSA-KEM Algorithm {#app-alg}

The RSA-KEM Algorithm is a one-pass (store-and-forward) cryptographic
mechanism for an originator to securely send keying material to a recipient
using the recipient's RSA public key.

With this type of algorithm, an originator encrypts the keying material
using the recipient's public key, and then sends the resulting encrypted
keying material to the recipient.  The recipient decrypts the encrypted
keying material using the recipient's private key to recover the keying
material.

A KEM algorithm provides three functions:

* KeyGen() -> (pk, sk):

    Generate the public key (pk) and a private key (sk).

* Encapsulate(pk) -> (ct, ss):

    Given the recipient's public key (pk), produce a ciphertext (ct) to be passed to the recipient and shared secret (ss) for the originator.

* Decapsulate(sk, ct) -> ss:

    Given the private key (sk) and the ciphertext (ct), produce the shared secret (ss) for the recipient.

## Underlying Components

The RSA-KEM Algorithm has the following underlying components:

- KDF, a key-derivation function, which derives key-encryption key of a
  specified length from a shared secret value;

The kekLen value denotes the length in bytes of the key-encryption key
for the underlying symmetric key-encryption algorithm.

Many key-derivation functions support the inclusion of other information
in addition to the shared secret value in the input to the function.
Also, with some symmetric key-encryption algorithms, it is possible to
associate a label with the keying material.  Such uses are outside the scope
of this document, as they are not directly supported by CMS.

## KeyGen()

The key generation for RSA-KEM proceeds as per [RFC8017].

## Encapsulate() {#app-alg-encaps}

The RSA-KEM algorithm denoted by `id-kem-rsa` fulfills the generic `KEM.Encapsulate(pk) -> (ct, ss)` interface as discribed below.

Let `pk= (n,e)` be the recipient's RSA public key; see {{RFC8017}} for details.

Let nLen denote the length in bytes of the modulus n, i.e., the least
integer such that 2^(8*nLen) > n.

Let kekLen be the desired length of the shared secret to output.

The originator performs the following operations:

1. Generate a random integer z between 0 and n-1 (see note), and
   convert z to a byte string Z of length nLen, most significant byte
   first:

   ~~~
        z = RandomInteger (0, n-1)

        Z = IntegerToString (z, nLen)
   ~~~

2. Encrypt the random integer z using the recipient's RSA public key
   (n,e), and convert the resulting integer c to a ciphertext C, a
   byte string of length nLen:

   ~~~
        c = z^e mod n

        C = IntegerToString (c, nLen)
   ~~~

3. Derive a symmetric key-encryption key KEK of length kekLen bytes
   from the byte string Z using the underlying key-derivation function:

   ~~~
        KEK = KDF (Z, kekLen)
   ~~~

4. Return the ciphertext C and the shared secret KEK.

NOTE: The random integer z MUST be generated independently at random
for different encryption operations, whether for the same or
different recipients.

## Decapsulate() {#app-alg-decaps}

The RSA-KEM algorithm denoted by `id-kem-rsa` fulfills the generic `KEM.Decapsulate(sk, ct) -> ss` interface as discribed below.

Let `sk = (n,d)` be the recipient's RSA private key; see {{RFC8017}} for details,
but other private key formats are allowed.

Let C be the ciphertext.

Let nLen denote the length in bytes of the modulus n.

Let kekLen be the desired length of the shared secret to output.

The recipient performs the following operations:

1. If the length of the ciphertext C is less than nLen
   bytes, output "decryption error", and stop.

2. Convert the ciphertext C to an integer c, most significant byte
   first.  Decrypt the integer c using the recipient's private key
   (n,d) to recover an integer z (see NOTE below):

   ~~~
        c = StringToInteger (C)

        z = c^d mod n
   ~~~

   If the integer c is not between 0 and n-1, output "decryption
   error", and stop.

3. Convert the integer z to a byte string Z of length nLen, most
   significant byte first (see NOTE below):

   ~~~
        Z = IntegerToString (z, nLen)
   ~~~

4. Derive a shared secret SS of length kekLen bytes from
   the byte string Z using the key-derivation function (see NOTE below):

   ~~~
        SS = KDF (Z, kekLen)
   ~~~

5. Output the shared secret SS.

SS can be used directly as a symmetric key.

NOTE: Implementations SHOULD NOT reveal information about the
integer z, the string Z, or about the calculation of the
exponentiation in Step 2, the conversion in Step 3, or the key
derivation in Step 4, whether by timing or other "side channels".
The observable behavior of the implementation SHOULD be the same at
these steps for all ciphertexts C that are in range.  For example,
IntegerToString conversion should take the same amount of time
regardless of the actual value of the integer z.  The integer z, the
string Z, and other intermediate results MUST be securely deleted
when they are no longer needed.



## Legacy RFC5990 RSA-KEM

Here we define the original behaviour of `id-rsa-kem` as specified in [RFC5990] which is compatible with CMS KeyTransRecipientInfo.

### Underlying Components

The RSA-KEM Algorithm as originally defined in [RFC5990] has the following underlying components:

- KDF, a key-derivation function, which derives key-encryption key of a
  specified length from a shared secret value;

- Wrap, a symmetric key-encryption algorithm, which encrypts keying material
  using key-encryption key that was produced by the KDF.

The kekLen value denotes the length in bytes of the key-encryption key
for the underlying symmetric key-encryption algorithm.

The length of the keying material MUST be among the lengths supported by
the underlying symmetric key-encryption algorithm.  For example, the
AES-Wrap key-encryption algorithm requires the kekLen to be 16, 24,
or 32 octets.  Usage and formatting of the keying material is outside
the scope of the RSA-KEM Algorithm.

Many key-derivation functions support the inclusion of other information
in addition to the shared secret value in the input to the function.
Also, with some symmetric key-encryption algorithms, it is possible to
associate a label with the keying material.  Such uses are outside the scope
of this document, as they are not directly supported by CMS.

### Originator's Operations

Let (n,e) be the recipient's RSA public key; see {{RFC8017}} for details.

Let K be the keying material to be securely transferred from the originator
to the recipient.

Let nLen denote the length in bytes of the modulus n, i.e., the least
integer such that 2^(8*nLen) > n.

The originator performs the following operations:

1. Generate a random integer z between 0 and n-1 (see note), and
   convert z to a byte string Z of length nLen, most significant byte
   first:

   ~~~
        z = RandomInteger (0, n-1)

        Z = IntegerToString (z, nLen)
   ~~~

2. Encrypt the random integer z using the recipient's RSA public key
   (n,e), and convert the resulting integer c to a ciphertext C, a
   byte string of length nLen:

   ~~~
        c = z^e mod n

        C = IntegerToString (c, nLen)
   ~~~

3. Derive a symmetric key-encryption key KEK of length kekLen bytes
   from the byte string Z using the underlying key-derivation function:

   ~~~
        KEK = KDF (Z, kekLen)
   ~~~

4. Wrap the keying material K with the symmetric key-encryption key
   KEK using the key-encryption algorithm to obtain wrapped keying
   material WK:

   ~~~
        WK = Wrap (KEK, K)
   ~~~

5. Send the ciphertext C and the wrapped keying material WK to the recipient.

NOTE: The random integer z MUST be generated independently at random
for different encryption operations, whether for the same or
different recipients.

### Recipient's Operations

Let (n,d) be the recipient's RSA private key; see {{RFC8017}} for details,
but other private key formats are allowed.

Let WK be the encrypted keying material.

Let C be the ciphertext.

Let nLen denote the length in bytes of the modulus n.

The recipient performs the following operations:

1. If the length of the encrypted keying material is less than nLen
   bytes, output "decryption error", and stop.

2. Convert the ciphertext C to an integer c, most significant byte
   first.  Decrypt the integer c using the recipient's private key
   (n,d) to recover an integer z (see NOTE below):

   ~~~
        c = StringToInteger (C)

        z = c^d mod n
   ~~~

   If the integer c is not between 0 and n-1, output "decryption
   error", and stop.

3. Convert the integer z to a byte string Z of length nLen, most
   significant byte first (see NOTE below):

   ~~~
        Z = IntegerToString (z, nLen)
   ~~~

4. Derive a symmetric key-encryption key KEK of length kekLen bytes from
   the byte string Z using the key-derivation function (see NOTE below):

   ~~~
        KEK = KDF (Z, kekLen)
   ~~~

5. Unwrap the wrapped keying material WK with the symmetric
   key-encryption key KEK using the underlying key-encryption
   algorithm to recover the keying material K:

   ~~~
        K = Unwrap (KEK, WK)
   ~~~

   If the unwrapping operation outputs an error, output "decryption
   error", and stop.

6. Output the keying material K.

NOTE: Implementations SHOULD NOT reveal information about the
integer z, the string Z, or about the calculation of the
exponentiation in Step 2, the conversion in Step 3, or the key
derivation in Step 4, whether by timing or other "side channels".
The observable behavior of the implementation SHOULD be the same at
these steps for all ciphertexts C that are in range.  For example,
IntegerToString conversion should take the same amount of time
regardless of the actual value of the integer z.  The integer z, the
string Z, and other intermediate results MUST be securely deleted
when they are no longer needed.

# ASN.1 Syntax {#app-asn1}

The ASN.1 syntax for identifying the RSA-KEM Algorithm
is an extension of the syntax for the "generic hybrid cipher" in
ANS X9.44 {{ANS-X9.44}}.

The ASN.1 Module is unchanged from RFC 5990.  The id-rsa-kem-spki
object identifier is used in a backward compatible manner
in certificates {{RFC5280}} and SMIMECapabilities {{RFC8551}}.
Of course, the use of the id-kem-rsa object identifier in the
new KEMRecipientInfo structure {{I-D.ietf-lamps-cms-kemri}}
was not yet defined at the time that RFC 5990 was written.

## Underlying Components {#app-asn1-intro}

Implementations that conform to this specification MUST support
the KDF3 {{ANS-X9.44}} key-derivation function using SHA-256 {{SHS}}.

The object identifier for KDF3 is:

~~~
   id-kdf-kdf3 OBJECT IDENTIFIER ::= { x9-44-components kdf3(2) }
~~~

The KDF3 parameters identify the underlying hash function.  For
alignment with the ANS X9.44, the hash function MUST be an ASC X9-approved
hash function.  While the SHA-1 hash algorithm is included in the
ASN.1 definitions, SHA-1 MUST NOT be used.  SHA-1 is considered
to be obsolete; see {{RFC6194}}.  SHA-1 remains in the ASN.1 module for
compatibility with RFC 5990.  In addition, other hash functions MAY be
used with CMS.

~~~
   kda-kdf3 KEY-DERIVATION ::= {
      IDENTIFIER id-kdf-kdf3
      PARAMS TYPE KDF3-HashFunction ARE required
      -- No S/MIME caps defined -- }

   KDF3-HashFunction ::=
      AlgorithmIdentifier { DIGEST-ALGORITHM, {KDF3-HashFunctions} }

   KDF3-HashFunctions DIGEST-ALGORITHM ::= { X9-HashFunctions, ... }

   X9-HashFunctions DIGEST-ALGORITHM ::= {
      mda-sha1 | mda-sha224 | mda-sha256 | mda-sha384 |
      mda-sha512, ... }
~~~

Implementations that conform to this specification MUST support
the AES Key Wrap {{RFC3394}} key-encryption algorithm with a 128-bit
key.  There are three object identifiers for the AES Key Wrap, one for
each permitted size of the key-encryption key.  There are three object
identifiers imported from {{RFC5912}}, and none of these algorithm
identifiers have associated parameters:

~~~
   kwa-aes128-wrap KEY-WRAP ::= {
       IDENTIFIER id-aes128-wrap
       PARAMS ARE absent
       SMIME-CAPS { IDENTIFIED BY id-aes128-wrap } }

   kwa-aes192-wrap KEY-WRAP ::= {
       IDENTIFIER id-aes192-wrap
       PARAMS ARE absent
       SMIME-CAPS { IDENTIFIED BY id-aes192-wrap } }

   kwa-aes256-wrap KEY-WRAP ::= {
       IDENTIFIER id-aes256-wrap
       PARAMS ARE absent
       SMIME-CAPS { IDENTIFIED BY id-aes256-wrap } }
~~~

## ASN.1 Module {#app-asn1-module}

RFC EDITOR: Please replace TBD2 with the value assigned by IANA
during the publication of {{I-D.ietf-lamps-cms-kemri}}.

~~~ asn.1
CMS-RSA-KEM-2023
   { iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1)
     pkcs-9(9) smime(16) modules(0) id-mod-cms-rsa-kem-2023(TBD1) }

DEFINITIONS ::= BEGIN

-- EXPORTS ALL

IMPORTS

  KEM-ALGORITHM
    FROM KEMAlgorithmInformation-2023  -- [I-D.ietf-lamps-cms-kemri]
       { iso(1) identified-organization(3) dod(6) internet(1)
         security(5) mechanisms(5) pkix(7) id-mod(0)
         id-mod-kemAlgorithmInformation-2023(TBD3) }

  AlgorithmIdentifier{}, PUBLIC-KEY, DIGEST-ALGORITHM,
  KEY-DERIVATION, KEY-WRAP
    FROM AlgorithmInformation-2009  -- [RFC5912]
      { iso(1) identified-organization(3) dod(6) internet(1)
        security(5) mechanisms(5) pkix(7) id-mod(0)
        id-mod-algorithmInformation-02(58) }

  kwa-aes128-wrap, kwa-aes192-wrap, kwa-aes256-wrap
    FROM CMSAesRsaesOaep-2009  -- [RFC5911]
      { iso(1) member-body(2) us(840) rsadsi(113549)
        pkcs(1) pkcs-9(9) smime(16) modules(0)
        id-mod-cms-aes-02(38) }

  kwa-3DESWrap
    FROM CryptographicMessageSyntaxAlgorithms-2009  -- [RFC5911]
      { iso(1) member-body(2) us(840) rsadsi(113549)
        pkcs(1) pkcs-9(9) smime(16) modules(0)
        id-mod-cmsalg-2001-02(37) }

  id-camellia128-wrap, id-camellia192-wrap, id-camellia256-wrap
    FROM CamelliaEncryptionAlgorithmInCMS  -- [RFC3657]
      { iso(1) member-body(2) us(840) rsadsi(113549)
        pkcs(1) pkcs9(9) smime(16) modules(0)
        id-mod-cms-camellia(23) }

  mda-sha1, pk-rsa, RSAPublicKey
    FROM PKIXAlgs-2009  -- [RFC5912]
      { iso(1) identified-organization(3) dod(6) internet(1)
        security(5) mechanisms(5) pkix(7) id-mod(0)
        id-mod-pkix1-algorithms2008-02(56) }

  mda-sha224, mda-sha256, mda-sha384, mda-sha512
    FROM PKIX1-PSS-OAEP-Algorithms-2009  -- [RFC5912]
      { iso(1) identified-organization(3) dod(6) internet(1)
        security(5) mechanisms(5) pkix(7) id-mod(0)
        id-mod-pkix1-rsa-pkalgs-02(54) } ;


-- Useful types and definitions

OID ::= OBJECT IDENTIFIER  -- alias

NullParms ::= NULL

-- ISO/IEC 18033-2 arc

is18033-2 OID ::= { iso(1) standard(0) is18033(18033) part2(2) }

-- NIST algorithm arc

nistAlgorithm OID ::= { joint-iso-itu-t(2) country(16) us(840)
   organization(1) gov(101) csor(3) nistAlgorithm(4) }

-- PKCS #1 arc

pkcs-1 OID ::= { iso(1) member-body(2) us(840) rsadsi(113549)
   pkcs(1) pkcs-1(1) }

-- X9.44 arc

x9-44 OID ::= { iso(1) identified-organization(3) tc68(133)
   country(16) x9(840) x9Standards(9) x9-44(44) }

x9-44-components OID ::= { x9-44 components(1) }

-- RSA-KEM Algorithm

id-rsa-kem OID ::= { iso(1) member-body(2) us(840) rsadsi(113549)
   pkcs(1) pkcs-9(9) smime(16) alg(3) 14 }

id-rsa-kem-spki OID ::= id-rsa-kem

GenericHybridParameters ::= SEQUENCE {
   kem  KeyEncapsulationMechanism,
   dem  DataEncapsulationMechanism }

KeyEncapsulationMechanism ::=
   AlgorithmIdentifier { KEM-ALGORITHM, {KEMAlgorithms} }

KEMAlgorithms KEM-ALGORITHM ::= { kema-kem-rsa | kema-rsa-kem, ... }

kema-rsa-kem KEM-ALGORITHM ::= {
   IDENTIFIER id-rsa-kem-spki
   PARAMS TYPE GenericHybridParameters ARE optional
   PUBLIC-KEYS { pk-rsa | pk-rsa-kem }
   UKM ARE optional
   SMIME-CAPS { TYPE GenericHybridParameters
      IDENTIFIED BY id-rsa-kem-spki } }

kema-kem-rsa KEM-ALGORITHM ::= {
   IDENTIFIER id-kem-rsa
   PARAMS TYPE RsaKemParameters ARE optional
   PUBLIC-KEYS { pk-rsa | pk-rsa-kem }
   UKM ARE optional
   SMIME-CAPS { TYPE GenericHybridParameters
      IDENTIFIED BY id-rsa-kem-spki } }

id-kem-rsa OID ::= { is18033-2 key-encapsulation-mechanism(2)
   rsa(4) }

RsaKemParameters ::= SEQUENCE {
   keyDerivationFunction  KeyDerivationFunction,
   keyLength              KeyLength }

pk-rsa-kem PUBLIC-KEY ::= {
  IDENTIFIER id-rsa-kem-spki
  KEY RSAPublicKey
  PARAMS TYPE GenericHybridParameters ARE preferredAbsent
  -- Private key format is not specified here --
  CERT-KEY-USAGE {keyEncipherment} }

KeyDerivationFunction ::=
   AlgorithmIdentifier { KEY-DERIVATION, {KDFAlgorithms} }

KDFAlgorithms KEY-DERIVATION ::= { kda-kdf2 | kda-kdf3, ... }

KeyLength ::= INTEGER (1..MAX)

DataEncapsulationMechanism ::=
   AlgorithmIdentifier { KEY-WRAP, {DEMAlgorithms} }

DEMAlgorithms KEY-WRAP ::= {
   X9-SymmetricKeyWrappingSchemes |
   Camellia-KeyWrappingSchemes, ... }

X9-SymmetricKeyWrappingSchemes KEY-WRAP ::= {
   kwa-aes128-wrap | kwa-aes192-wrap | kwa-aes256-wrap |
   kwa-3DESWrap, ... }

X9-SymmetricKeyWrappingScheme ::=
   AlgorithmIdentifier { KEY-WRAP, {X9-SymmetricKeyWrappingSchemes} }

Camellia-KeyWrappingSchemes KEY-WRAP ::= {
   kwa-camellia128-wrap | kwa-camellia192-wrap |
   kwa-camellia256-wrap, ... }

Camellia-KeyWrappingScheme ::=
   AlgorithmIdentifier { KEY-WRAP, {Camellia-KeyWrappingSchemes} }

kwa-camellia128-wrap KEY-WRAP ::= {
   IDENTIFIER id-camellia128-wrap
   PARAMS ARE absent
   SMIME-CAPS { IDENTIFIED BY id-camellia128-wrap } }

kwa-camellia192-wrap KEY-WRAP ::= {
   IDENTIFIER id-camellia192-wrap
   PARAMS ARE absent
   SMIME-CAPS { IDENTIFIED BY id-camellia192-wrap } }

kwa-camellia256-wrap KEY-WRAP ::= {
   IDENTIFIER id-camellia256-wrap
   PARAMS ARE absent
   SMIME-CAPS { IDENTIFIED BY id-camellia256-wrap } }

-- Key Derivation Functions

id-kdf-kdf2 OID ::= { x9-44-components kdf2(1) }

kda-kdf2 KEY-DERIVATION ::= {
   IDENTIFIER id-kdf-kdf2
   PARAMS TYPE KDF2-HashFunction ARE required
   -- No S/MIME caps defined -- }

KDF2-HashFunction ::=
   AlgorithmIdentifier { DIGEST-ALGORITHM, {KDF2-HashFunctions} }

KDF2-HashFunctions DIGEST-ALGORITHM ::= { X9-HashFunctions, ... }

id-kdf-kdf3 OID ::= { x9-44-components kdf3(2) }

kda-kdf3 KEY-DERIVATION ::= {
   IDENTIFIER id-kdf-kdf3
   PARAMS TYPE KDF3-HashFunction ARE required
   -- No S/MIME caps defined -- }

KDF3-HashFunction ::=
   AlgorithmIdentifier { DIGEST-ALGORITHM, {KDF3-HashFunctions} }

KDF3-HashFunctions DIGEST-ALGORITHM ::= { X9-HashFunctions, ... }

-- Hash Functions

X9-HashFunctions DIGEST-ALGORITHM ::= {
   mda-sha1 | mda-sha224 | mda-sha256 | mda-sha384 |
   mda-sha512, ... }

END
~~~
{: sourcecode-markers='true'}

# SMIMECapabilities Examples {#app-example}

To indicate support for the RSA-KEM algorithm coupled with the KDF3
key-derivation function with SHA-256 and the AES Key Wrap symmetric
key-encryption algorithm 128-bit key-encryption key, the
SMIMECapabilities will include the following entry:

~~~
SEQUENCE {
   id-rsa-kem-spki,                           -- RSA-KEM Algorithm
   SEQUENCE {                           -- GenericHybridParameters
      SEQUENCE {                    -- key encapsulation mechanism
         id-kem-rsa,                                    -- RSA-KEM
         SEQUENCE {                            -- RsaKemParameters
            SEQUENCE {                  -- key derivation function
               id-kdf-kdf3,                                -- KDF3
               SEQUENCE {                     -- KDF3-HashFunction
                  id-sha256  -- SHA-256; no parameters (preferred)
               },
            16                              -- KEK length in bytes
            },
      SEQUENCE {                   -- data encapsulation mechanism
         id-aes128-Wrap             -- AES-128 Wrap; no parameters
      }
   }
}
~~~

This SMIMECapability value has the following DER encoding (in hexadecimal):

~~~
30 47
  06 0b 2a 86 48 86 f7 0d 01 09 10 03 0e          -- id-rsa-kem-spki
  30 38
     30 29
        06 07 28 81 8c 71 02 02 04                -- id-kem-rsa
        30 1e
           30 19
              06 0a 2b 81 05 10 86 48 09 2c 01 02 -- id-kdf-kdf3
              30 0b
                 06 09 60 86 48 01 65 03 04 02 01 -- id-sha256
                 02 01 10                         -- 16 bytes
      30 0b
         06 09 60 86 48 01 65 03 04 01 05         -- id-aes128-Wrap
~~~

To indicate support for the RSA-KEM algorithm coupled with the KDF3
key-derivation function with SHA-384 and the AES Key Wrap symmetric
key-encryption algorithm 192-bit key-encryption key, the
SMIMECapabilities will include the following SMIMECapability value
(in hexadecimal):

~~~
  30 47 06 0b 2a 86 48 86 f7 0d 01 09 10 03 0e 30
  38 30 29 06 07 28 81 8c 71 02 02 04 30 1e 30 19
  06 0a 2b 81 05 10 86 48 09 2c 01 02 30 0b 06 09
  60 86 48 01 65 03 04 02 02 02 01 18 30 0b 06 09
  60 86 48 01 65 03 04 01 19
~~~

To indicate support for the RSA-KEM algorithm coupled with the KDF3
key-derivation function with SHA-512 and the AES Key Wrap symmetric
key-encryption algorithm 256-bit key-encryption key, the
SMIMECapabilities will include the following SMIMECapability value
(in hexadecimal):

~~~
  30 47 06 0b 2a 86 48 86 f7 0d 01 09 10 03 0e 30
  38 30 29 06 07 28 81 8c 71 02 02 04 30 1e 30 19
  06 0a 2b 81 05 10 86 48 09 2c 01 02 30 0b 06 09
  60 86 48 01 65 03 04 02 03 02 01 20 30 0b 06 09
  60 86 48 01 65 03 04 01 2d
~~~


# RSA-KEM CMS Enveloped-Data Example

This example shows the establishment of an AES-128 content-encryption
key using:

- RSA-KEM with a 3072-bit key;
- key derivation using KDF2 with SHA-256; and
- key wrap using AES-128-KEYWRAP.

In real-world use, the originator would encrypt the content-encryption
key in a manner that would allow decryption with their own private key
as well as the recipient's private key.  This is omitted in an attempt
to simplify the example.

## Originator Processing

Alice obtains Bob's public key:

~~~
   -----BEGIN PUBLIC KEY-----
   MIIBojANBgkqhkiG9w0BAQEFAAOCAY8AMIIBigKCAYEA3ocW14cxncPJ47fnEjBZ
   AyfC2lqapL3ET4jvV6C7gGeVrRQxWPDwl+cFYBBR2ej3j3/0ecDmu+XuVi2+s5JH
   Keeza+itfuhsz3yifgeEpeK8T+SusHhn20/NBLhYKbh3kiAcCgQ56dpDrDvDcLqq
   vS3jg/VO+OPnZbofoHOOevt8Q/roahJe1PlIyQ4udWB8zZezJ4mLLfbOA9YVaYXx
   2AHHZJevo3nmRnlgJXo6mE00E/6qkhjDHKSMdl2WG6mO9TCDZc9qY3cAJDU6Ir0v
   SH7qUl8/vN13y4UOFkn8hM4kmZ6bJqbZt5NbjHtY4uQ0VMW3RyESzhrO02mrp39a
   uLNnH3EXdXaV1tk75H3qC7zJaeGWMJyQfOE3YfEGRKn8fxubji716D8UecAxAzFy
   FL6m1JiOyV5acAiOpxN14qRYZdHnXOM9DqGIGpoeY1UuD4Mo05osOqOUpBJHA9fS
   whSZG7VNf+vgNWTLNYSYLI04KiMdulnvU6ds+QPz+KKtAgMBAAE=
   -----END PUBLIC KEY-----
~~~

Bob's RSA public key has the following key identifier:

~~~
   9eeb67c9b95a74d44d2f16396680e801b5cba49c
~~~

Alice randomly generates integer z between 0 and n-1:

~~~
   9c126102a5c1c0354672a3c2f19fc9ddea988f815e1da812c7bd4f8eb082bdd1
   4f85a7f7c2f1af11d5333e0d6bcb375bf855f208da72ba27e6fb0655f2825aa6
   2b93b1f9bbd3491fed58f0380fa0de36430e3a144d569600bd362609be5b9481
   0875990b614e406fa6dff500043cbca95968faba61f795096a7fb3687a51078c
   4ca2cb663366b0bea0cd9cccac72a25f3f4ed03deb68b4453bba44b943f4367b
   67d6cd10c8ace53f545aac50968fc3c6ecc80f3224b64e37038504e2d2c0e2b2
   9d45e46c62826d96331360e4c17ea3ef89a9efc5fac99eda830e81450b6534dc
   0bdf042b8f3b706649c631fe51fc2445cc8d447203ec2f41f79cdfea16de1ce6
   abdfdc1e2ef2e5d5d8a65e645f397240ef5a26f5e4ff715de782e30ecf477293
   e89e13171405909a8e04dd31d21d0c57935fc1ceea8e1033e31e1bc8c56da0f3
   d79510f3f380ff58e5a61d361f2f18e99fbae5663172e8cd1f21deaddc5bbbea
   060d55f1842b93d1a9c888d0bf85d0af9947fe51acf940c7e7577eb79cabecb3
~~~

Alice encrypts integer z using the Bob's RSA public key, the result is
called c:

~~~
   c071fc273af8e7bdb152e06bf73310361074154a43abcf3c93c13499d2065344
   3eed9ef5d3c0685e4aa76a6854815bb97691ff9f8dac15eea7d74f452bf350a6
   46163d68288e978cbf7a73089ee52712f9a4f49e06ace7bbc85ab14d4e336c97
   c5728a2654138c7b26e8835c6b0a9fbed26495c4eadf745a2933be283f6a88b1
   6695fc06666873cfb6d36718ef3376cefc100c3941f3c494944078325807a559
   186b95ccabf3714cfaf79f83bd30537fdd9aed5a4cdcbd8bd0486faed73e9d48
   6b3087d6c806546b6e2671575c98461e441f65542bd95de26d0f53a64e7848d7
   31d9608d053e8d345546602d86236ffe3704c98ad59144f3089e5e6d527b5497
   ba103c79d62e80d0235410b06f71a7d9bd1c38000f910d6312ea2f20a3557535
   ad01b3093fb5f7ee507080d0f77d48c9c3b3796f6b7dd3786085fb895123f04c
   a1f1c1be22c747a8dface32370fb0d570783e27dbb7e74fca94ee39676fde3d8
   a9553d878224736e37e191dab953c7e228c07ad5ca3122421c14debd072a9ab6
~~~

Alice encodes the CMSORIforKEMOtherInfo structure with the algorithm
identifier for AES-128-KEYWRAP and a key length of 16 octets.
The DER encoding of CMSORIforKEMOtherInfo produces 18 octets:

~~~
   3010300b0609608648016503040105020110
~~~

The CMSORIforKEMOtherInfo structure contains:

>
~~~
  0  16: SEQUENCE {
  2  11:  SEQUENCE {
  4   9:   OBJECT IDENTIFIER aes128-wrap (2 16 840 1 101 3 4 1 5)
       :    }
 15   1:  INTEGER 16
       :   }
~~~

Alice derives the key-encryption key from integer z and the
CMSORIforKEMOtherInfo structure with KDF2 and SHA-256, the KEK is:

~~~
   4a95fe82f8d6ba56c83b4d51ef7dc06b
~~~

Alice randomly generates a 128-bit content-encryption key:

~~~
   77f2a84640304be7bd42670a84a1258b
~~~

Alice uses AES-128-KEYWRAP to encrypt the 128-bit content-encryption
key with the derived key-encryption key:

~~~
   904dbeb0271fc02082fe6d358c03352ae4ae6b540b782423
~~~

Alice encrypts the padded content using AES-128-CBC with the
content-encryption key.  The 16-octet IV used is:

~~~
   480ccafebabefacedbaddecaf8887781
~~~

The padded content plaintext is:

~~~
   48656c6c6f2c20776f726c6421030303
~~~

The resulting ciphertext is:

~~~
   c6ca65db7bdd76b0f37e2fab6264b66d
~~~

## ContentInfo and EnvelopedData

Alice encodes the EnvelopedData (using KEMRecipientInfo) and
ContentInfo, and then sends the result to Bob.  The Base64-encoded:
result is:

>
~~~
MIICXAYJKoZIhvcNAQcDoIICTTCCAkkCAQMxggIEpIICAAYLKoZIhvcNAQkQDQMwggH
vAgEAgBSe62fJuVp01E0vFjlmgOgBtcuknDAJBgcogYxxAgIEBIIBgMBx/Cc6+Oe9sV
Lga/czEDYQdBVKQ6vPPJPBNJnSBlNEPu2e9dPAaF5Kp2poVIFbuXaR/5+NrBXup9dPR
SvzUKZGFj1oKI6XjL96cwie5ScS+aT0ngas57vIWrFNTjNsl8VyiiZUE4x7JuiDXGsK
n77SZJXE6t90Wikzvig/aoixZpX8BmZoc8+202cY7zN2zvwQDDlB88SUlEB4MlgHpVk
Ya5XMq/NxTPr3n4O9MFN/3ZrtWkzcvYvQSG+u1z6dSGswh9bIBlRrbiZxV1yYRh5EH2
VUK9ld4m0PU6ZOeEjXMdlgjQU+jTRVRmAthiNv/jcEyYrVkUTzCJ5ebVJ7VJe6EDx51
i6A0CNUELBvcafZvRw4AA+RDWMS6i8go1V1Na0Bswk/tffuUHCA0Pd9SMnDs3lva33T
eGCF+4lRI/BMofHBviLHR6jfrOMjcPsNVweD4n27fnT8qU7jlnb949ipVT2HgiRzbjf
hkdq5U8fiKMB61coxIkIcFN69ByqatjAbBgorgQUQhkgJLAEBMA0GCWCGSAFlAwQCAQ
UAAgEQMAsGCWCGSAFlAwQBBQQYkE2+sCcfwCCC/m01jAM1KuSua1QLeCQjMDwGCSqGS
Ib3DQEHATAdBglghkgBZQMEAQIEEEgMyv66vvrO263eyviId4GAEMbKZdt73Xaw834v
q2Jktm0=
~~~

This result decodes to:

>
~~~
  0 604: SEQUENCE {
  4   9:  OBJECT IDENTIFIER envelopedData (1 2 840 113549 1 7 3)
 15 589:  [0] {
 19 585:   SEQUENCE {
 23   1:    INTEGER 3
 26 516:    SET {
 30 512:     [4] {
 34  11:      OBJECT IDENTIFIER
       :       KEMRecipientInfo (1 2 840 113549 1 9 16 13 3)
 47 495:      SEQUENCE {
 51   1:       INTEGER 0
 54  20:       [0]
       :       9E EB 67 C9 B9 5A 74 D4 4D 2F 16 39 66 80 E8 01
       :       B5 CB A4 9C
 76   9:       SEQUENCE {
 78   7:        OBJECT IDENTIFIER kemRSA (1 0 18033 2 2 4)
       :         }
 87 384:       OCTET STRING
       :       C0 71 FC 27 3A F8 E7 BD B1 52 E0 6B F7 33 10 36
       :       10 74 15 4A 43 AB CF 3C 93 C1 34 99 D2 06 53 44
       :       3E ED 9E F5 D3 C0 68 5E 4A A7 6A 68 54 81 5B B9
       :       76 91 FF 9F 8D AC 15 EE A7 D7 4F 45 2B F3 50 A6
       :       46 16 3D 68 28 8E 97 8C BF 7A 73 08 9E E5 27 12
       :       F9 A4 F4 9E 06 AC E7 BB C8 5A B1 4D 4E 33 6C 97
       :       C5 72 8A 26 54 13 8C 7B 26 E8 83 5C 6B 0A 9F BE
       :       D2 64 95 C4 EA DF 74 5A 29 33 BE 28 3F 6A 88 B1
       :       66 95 FC 06 66 68 73 CF B6 D3 67 18 EF 33 76 CE
       :       FC 10 0C 39 41 F3 C4 94 94 40 78 32 58 07 A5 59
       :       18 6B 95 CC AB F3 71 4C FA F7 9F 83 BD 30 53 7F
       :       DD 9A ED 5A 4C DC BD 8B D0 48 6F AE D7 3E 9D 48
       :       6B 30 87 D6 C8 06 54 6B 6E 26 71 57 5C 98 46 1E
       :       44 1F 65 54 2B D9 5D E2 6D 0F 53 A6 4E 78 48 D7
       :       31 D9 60 8D 05 3E 8D 34 55 46 60 2D 86 23 6F FE
       :       37 04 C9 8A D5 91 44 F3 08 9E 5E 6D 52 7B 54 97
       :       BA 10 3C 79 D6 2E 80 D0 23 54 10 B0 6F 71 A7 D9
       :       BD 1C 38 00 0F 91 0D 63 12 EA 2F 20 A3 55 75 35
       :       AD 01 B3 09 3F B5 F7 EE 50 70 80 D0 F7 7D 48 C9
       :       C3 B3 79 6F 6B 7D D3 78 60 85 FB 89 51 23 F0 4C
       :       A1 F1 C1 BE 22 C7 47 A8 DF AC E3 23 70 FB 0D 57
       :       07 83 E2 7D BB 7E 74 FC A9 4E E3 96 76 FD E3 D8
       :       A9 55 3D 87 82 24 73 6E 37 E1 91 DA B9 53 C7 E2
       :       28 C0 7A D5 CA 31 22 42 1C 14 DE BD 07 2A 9A B6
475  27:       SEQUENCE {
477  10:        OBJECT IDENTIFIER
       :         kdf2 (1 3 133 16 840 9 44 1 1)
489  13:        SEQUENCE {
491   9:         OBJECT IDENTIFIER
       :          sha-256 (2 16 840 1 101 3 4 2 1)
502   0:         NULL
       :          }
       :         }
504   1:       INTEGER 16
507  11:       SEQUENCE {
509   9:        OBJECT IDENTIFIER
       :         aes128-wrap (2 16 840 1 101 3 4 1 5)
       :         }
520  24:       OCTET STRING
       :       90 4D BE B0 27 1F C0 20 82 FE 6D 35 8C 03 35 2A
       :       E4 AE 6B 54 0B 78 24 23
       :        }
       :       }
       :      }
546  60:    SEQUENCE {
548   9:     OBJECT IDENTIFIER data (1 2 840 113549 1 7 1)
559  29:     SEQUENCE {
561   9:      OBJECT IDENTIFIER
       :       aes128-CBC (2 16 840 1 101 3 4 1 2)
572  16:      OCTET STRING
       :      48 0C CA FE BA BE FA CE DB AD DE CA F8 88 77 81
       :       }
590  16:     [0] C6 CA 65 DB 7B DD 76 B0 F3 7E 2F AB 62 64 B6 6D
       :      }
       :     }
       :    }
       :   }
~~~

## Recipient Processing

Bob's private key:

~~~
   -----BEGIN PRIVATE KEY-----
   MIIG5AIBAAKCAYEA3ocW14cxncPJ47fnEjBZAyfC2lqapL3ET4jvV6C7gGeVrRQx
   WPDwl+cFYBBR2ej3j3/0ecDmu+XuVi2+s5JHKeeza+itfuhsz3yifgeEpeK8T+Su
   sHhn20/NBLhYKbh3kiAcCgQ56dpDrDvDcLqqvS3jg/VO+OPnZbofoHOOevt8Q/ro
   ahJe1PlIyQ4udWB8zZezJ4mLLfbOA9YVaYXx2AHHZJevo3nmRnlgJXo6mE00E/6q
   khjDHKSMdl2WG6mO9TCDZc9qY3cAJDU6Ir0vSH7qUl8/vN13y4UOFkn8hM4kmZ6b
   JqbZt5NbjHtY4uQ0VMW3RyESzhrO02mrp39auLNnH3EXdXaV1tk75H3qC7zJaeGW
   MJyQfOE3YfEGRKn8fxubji716D8UecAxAzFyFL6m1JiOyV5acAiOpxN14qRYZdHn
   XOM9DqGIGpoeY1UuD4Mo05osOqOUpBJHA9fSwhSZG7VNf+vgNWTLNYSYLI04KiMd
   ulnvU6ds+QPz+KKtAgMBAAECggGATFfkSkUjjJCjLvDk4aScpSx6+Rakf2hrdS3x
   jwqhyUfAXgTTeUQQBs1HVtHCgxQd+qlXYn3/qu8TeZVwG4NPztyi/Z5yB1wOGJEV
   3k8N/ytul6pJFFn6p48VM01bUdTrkMJbXERe6g/rr6dBQeeItCaOK7N5SIJH3Oqh
   9xYuB5tH4rquCdYLmt17Tx8CaVqU9qPY3vOdQEOwIjjMV8uQUR8rHSO9KkSj8AGs
   Lq9kcuPpvgJc2oqMRcNePS2WVh8xPFktRLLRazgLP8STHAtjT6SlJ2UzkUqfDHGK
   q/BoXxBDu6L1VDwdnIS5HXtL54ElcXWsoOyKF8/ilmhRUIUWRZFmlS1ok8IC5IgX
   UdL9rJVZFTRLyAwmcCEvRM1asbBrhyEyshSOuN5nHJi2WVJ+wSHijeKl1qeLlpMk
   HrdIYBq4Nz7/zXmiQphpAy+yQeanhP8O4O6C8e7RwKdpxe44su4Z8fEgA5yQx0u7
   8yR1EhGKydX5bhBLR5Cm1VM7rT2BAoHBAP/+e5gZLNf/ECtEBZjeiJ0VshszOoUq
   haUQPA+9Bx9pytsoKm5oQhB7QDaxAvrn8/FUW2aAkaXsaj9F+/q30AYSQtExai9J
   fdKKook3oimN8/yNRsKmhfjGOj8hd4+GjX0qoMSBCEVdT+bAjjry8wgQrqReuZnu
   oXU85dmb3jvv0uIczIKvTIeyjXE5afjQIJLmZFXsBm09BG87Ia5EFUKly96BOMJh
   /QWEzuYYXDqOFfzQtkAefXNFW21Kz4Hw2QKBwQDeiGh4lxCGTjECvG7fauMGlu+q
   DSdYyMHif6t6mx57eS16EjvOrlXKItYhIyzW8Kw0rf/CSB2j8ig1GkMLTOgrGIJ1
   0322o50FOr5oOmZPueeR4pOyAP0fgQ8DD1L3JBpY68/8MhYbsizVrR+Ar4jM0f96
   W2bF5Xj3h+fQTDMkx6VrCCQ6miRmBUzH+ZPs5n/lYOzAYrqiKOanaiHy4mjRvlsy
   mjZ6z5CG8sISqcLQ/k3Qli5pOY/v0rdBjgwAW/UCgcEAqGVYGjKdXCzuDvf9EpV4
   mpTWB6yIV2ckaPOn/tZi5BgsmEPwvZYZt0vMbu28Px7sSpkqUuBKbzJ4pcy8uC3I
   SuYiTAhMiHS4rxIBX3BYXSuDD2RD4vG1+XM0h6jVRHXHh0nOXdVfgnmigPGz3jVJ
   B8oph/jD8O2YCk4YCTDOXPEi8Rjusxzro+whvRR+kG0gsGGcKSVNCPj1fNISEte4
   gJId7O1mUAAzeDjn/VaS/PXQovEMolssPPKn9NocbKbpAoHBAJnFHJunl22W/lrr
   ppmPnIzjI30YVcYOA5vlqLKyGaAsnfYqP1WUNgfVhq2jRsrHx9cnHQI9Hu442PvI
   x+c5H30YFJ4ipE3eRRRmAUi4ghY5WgD+1hw8fqyUW7E7l5LbSbGEUVXtrkU5G64T
   UR91LEyMF8OPATdiV/KD4PWYkgaqRm3tVEuCVACDTQkqNsOOi3YPQcm270w6gxfQ
   SOEy/kdhCFexJFA8uZvmh6Cp2crczxyBilR/yCxqKOONqlFdOQKBwFbJk5eHPjJz
   AYueKMQESPGYCrwIqxgZGCxaqeVArHvKsEDx5whI6JWoFYVkFA8F0MyhukoEb/2x
   2qB5T88Dg3EbqjTiLg3qxrWJ2OxtUo8pBP2I2wbl2NOwzcbrlYhzEZ8bJyxZu5i1
   sYILC8PJ4Qzw6jS4Qpm4y1WHz8e/ElW6VyfmljZYA7f9WMntdfeQVqCVzNTvKn6f
   hg6GSpJTzp4LV3ougi9nQuWXZF2wInsXkLYpsiMbL6Fz34RwohJtYA==
   -----END PRIVATE KEY-----
~~~

Bob decrypts the integer z with his RSA private key:

~~~
   9c126102a5c1c0354672a3c2f19fc9ddea988f815e1da812c7bd4f8eb082bdd1
   4f85a7f7c2f1af11d5333e0d6bcb375bf855f208da72ba27e6fb0655f2825aa6
   2b93b1f9bbd3491fed58f0380fa0de36430e3a144d569600bd362609be5b9481
   0875990b614e406fa6dff500043cbca95968faba61f795096a7fb3687a51078c
   4ca2cb663366b0bea0cd9cccac72a25f3f4ed03deb68b4453bba44b943f4367b
   67d6cd10c8ace53f545aac50968fc3c6ecc80f3224b64e37038504e2d2c0e2b2
   9d45e46c62826d96331360e4c17ea3ef89a9efc5fac99eda830e81450b6534dc
   0bdf042b8f3b706649c631fe51fc2445cc8d447203ec2f41f79cdfea16de1ce6
   abdfdc1e2ef2e5d5d8a65e645f397240ef5a26f5e4ff715de782e30ecf477293
   e89e13171405909a8e04dd31d21d0c57935fc1ceea8e1033e31e1bc8c56da0f3
   d79510f3f380ff58e5a61d361f2f18e99fbae5663172e8cd1f21deaddc5bbbea
   060d55f1842b93d1a9c888d0bf85d0af9947fe51acf940c7e7577eb79cabecb3
~~~

Bob encodes the CMSORIforKEMOtherInfo structure with the algorithm
identifier for AES-128-KEYWRAP and a key length of 16 octets.
The DER encoding of CMSORIforKEMOtherInfo is not repeated here.

Bob derives the key-encryption key from integer z and the
CMSORIforKEMOtherInfo structure with KDF2 and SHA-256, the KEK is:

~~~
   4a95fe82f8d6ba56c83b4d51ef7dc06b
~~~

Bob uses AES-KEY-WRAP to decrypt the content-encryption key
with the key-encryption key; the content-encryption key is:

~~~
   77f2a84640304be7bd42670a84a1258b
~~~

Bob decrypts the content using AES-128-CBC with the content-
encryption key.  The 16-octet IV used is:

~~~
   480ccafebabefacedbaddecaf8887781
~~~

The received ciphertext content is:

~~~
   c6ca65db7bdd76b0f37e2fab6264b66d
~~~

The resulting padded plaintext content is:

~~~
   48656c6c6f2c20776f726c6421030303
~~~

After stripping the padding, the plaintext content is:

~~~
   Hello, world!
~~~


# Acknowledgements
{:numbered="false"}

We thank James Randall, Burt Kaliski, and John Brainard as the
original authors of {{RFC5990}}; this document is based on their work.

We thank the members of the ASC X9F1 working group for their
contributions to drafts of ANS X9.44, which led to {{RFC5990}}.

We thank Blake Ramsdell, Jim Schaad, Magnus Nystrom, Bob Griffin,
and John Linn for helping bring {{RFC5990}} to fruition.
