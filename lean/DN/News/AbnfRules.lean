-- SPDX-License-Identifier: AGPL-3.0-or-later AND BSD-3-Clause
import DN.News.Abnf

/-!
# DN.News.AbnfRules

The grammar of a Netnews article's header fields, as `scripts/gen_abnf.py` takes it from the
RFCs in `rfcs/`: that script says where each rule comes from and where, and why, it differs
from an RFC's text, and writes this file, which a check keeps current. Rules refer to each
other by their place in `grammar`, which is the order of their names.

## Notice

This code was derived from IETF RFC 5536, RFC 8315, RFC 5322, RFC 5234, RFC 3986, RFC 2045 and
RFC 2231, changed where a rule's note says. Please reproduce this note if possible.

Copyright (c) 2009, 2018 IETF Trust and the persons identified as authors of the code (RFC 5536,
RFC 8315). Copyright (C) The IETF Trust (2008) (RFC 5322, RFC 5234). Copyright (C) The Internet
Society (2005) (RFC 3986). All rights reserved.

Redistribution and use in source and binary forms, with or without modification, is permitted
pursuant to, and subject to the license terms contained in, the Revised BSD License set forth in
Section 4.c of the IETF Trust's Legal Provisions Relating to IETF Documents
(https://trustee.ietf.org/license-info).

RFC 2231: Copyright (C) The Internet Society (1997). All Rights Reserved.

This document and translations of it may be copied and furnished to others, and derivative works
that comment on or otherwise explain it or assist in its implementation may be prepared, copied,
published and distributed, in whole or in part, without restriction of any kind, provided that the
above copyright notice and this paragraph are included on all such copies and derivative works.
However, this document itself may not be modified in any way, such as by removing the copyright
notice or references to the Internet Society or other Internet organizations, except as needed for
the purpose of developing Internet standards in which case the procedures for copyrights defined in
the Internet Standards process must be followed, or as required to translate it into languages other
than English.

-/

namespace DN.News.AbnfRules

open DN.News.Abnf

/-- `addr-spec = local-part "@" domain` (RFC 5322) -/
def rAddrSpec : Term := .seq [.ref 90, .text "@", .ref 55]

/-- `address = mailbox / group` (RFC 5322) -/
def rAddress : Term := .alt [.ref 93, .ref 73]

/-- `address-list = address *("," address)` (RFC 5322) -/
def rAddressList : Term := .seq [.ref 1, .rep 0 none (.seq [.text ",", .ref 1])]

/-- `alpha = %x41-5A / %x61-7A` (RFC 5234) -/
def rAlpha : Term := .alt [.range 65 90, .range 97 122]

/-- `alphanum = alpha / digit` (RFC 5536) -/
def rAlphanum : Term := .alt [.ref 3, .ref 50]

/-- `angle-addr = [cfws] "<" addr-spec ">" [cfws]` (RFC 5322) -/
def rAngleAddr : Term := .seq [.rep 0 (some 1) (.ref 29), .text "<", .ref 0, .text ">", .rep 0 (some
    1) (.ref 29)]

/-- `approved = "Approved:" sp mailbox-list crlf` (RFC 5536) -/
def rApproved : Term := .seq [.text "Approved:", .ref 148, .ref 94, .ref 37]

/-- `archive = "Archive:" sp [cfws] ("no" / "yes") *([cfws] ";" [cfws] archive-param) [cfws]
crlf` (RFC 5536) -/
def rArchive : Term := .seq [.text "Archive:", .ref 148, .rep 0 (some 1) (.ref 29), .alt [.text
    "no", .text "yes"], .rep 0 none (.seq [.rep 0 (some 1) (.ref 29), .text ";", .rep 0 (some 1)
    (.ref 29), .ref 8]), .rep 0 (some 1) (.ref 29), .ref 37]

/-- `archive-param = parameter` (RFC 5536) -/
def rArchiveParam : Term := .ref 114

/-- `argument = 1*%x21-7E` (RFC 5536) -/
def rArgument : Term := .rep 1 none (.range 33 126)

/-- `article-locator = 1*(%x21-27 / %x29-3A / %x3C-7E)` (RFC 5536) -/
def rArticleLocator : Term := .rep 1 none (.alt [.range 33 39, .range 41 58, .range 60 126])

/-- `atext = alpha / digit / "!" / "#" / "$" / "%" / "&" / "'" / "*" / "+" / "-" / "/" / "=" /
"?" / "^" / "_" / "`" / "{" / "|" / "}" / "~"` (RFC 5322) -/
def rAtext : Term := .alt [.ref 3, .ref 50, .text "!", .text "#", .text "$", .text "%", .text "&",
    .text "'", .text "*", .text "+", .text "-", .text "/", .text "=", .text "?", .text "^", .text
    "_", .text "`", .text "{", .text "|", .text "}", .text "~"]

/-- `atom = [cfws] 1*atext [cfws]` (RFC 5322) -/
def rAtom : Term := .seq [.rep 0 (some 1) (.ref 29), .rep 1 none (.ref 11), .rep 0 (some 1) (.ref
    29)]

/-- `attribute = 1*attribute-char` (RFC 2231 §7) -/
def rAttribute : Term := .rep 1 none (.ref 14)

/-- `attribute-char = %x21 / %x23-24 / %x26 / %x2B / %x2D-2E / %x30-39 / %x41-5A / %x5E-7E` (RFC
2231 §7) -/
def rAttributeChar : Term := .alt [.range 33 33, .range 35 36, .range 38 38, .range 43 43, .range 45
    46, .range 48 57, .range 65 90, .range 94 126]

/-- `base64-char = alpha / digit / "+" / "/"` (RFC 8315) -/
def rBase64Char : Term := .alt [.ref 3, .ref 50, .text "+", .text "/"]

/-- `base64-octet = alpha / digit / "+" / "/" / "="` (RFC 8315) -/
def rBase64Octet : Term := .alt [.ref 3, .ref 50, .text "+", .text "/", .text "="]

/-- `base64-terminal = 2base64-char "==" / 3base64-char "="` (RFC 8315) -/
def rBase64Terminal : Term := .alt [.seq [.rep 2 (some 2) (.ref 15), .text "=="], .seq [.rep 3 (some
    3) (.ref 15), .text "="]]

/-- `bcc = "Bcc:" sp [address-list / cfws] crlf` (RFC 5322, with a space after the colon, as RFC
5536 §2.2 asks of every field) -/
def rBcc : Term := .seq [.text "Bcc:", .ref 148, .rep 0 (some 1) (.alt [.ref 2, .ref 29]), .ref 37]

/-- `c-key = scheme ":" c-key-string` (RFC 8315) -/
def rCKey : Term := .seq [.ref 142, .text ":", .ref 21]

/-- `c-key-list = [cfws] c-key *(cfws c-key) [cfws]` (RFC 8315) -/
def rCKeyList : Term := .seq [.rep 0 (some 1) (.ref 29), .ref 19, .rep 0 none (.seq [.ref 29, .ref
    19]), .rep 0 (some 1) (.ref 29)]

/-- `c-key-string = c-lock-string / obs-c-key-string` (RFC 8315) -/
def rCKeyString : Term := .alt [.ref 24, .ref 106]

/-- `c-lock = scheme ":" c-lock-string` (RFC 8315) -/
def rCLock : Term := .seq [.ref 142, .text ":", .ref 24]

/-- `c-lock-list = [cfws] c-lock *(cfws c-lock) [cfws]` (RFC 8315) -/
def rCLockList : Term := .seq [.rep 0 (some 1) (.ref 29), .ref 22, .rep 0 none (.seq [.ref 29, .ref
    22]), .rep 0 (some 1) (.ref 29)]

/-- `c-lock-string = *(4base64-char) [base64-terminal]` (RFC 8315) -/
def rCLockString : Term := .seq [.rep 0 none (.rep 4 (some 4) (.ref 15)), .rep 0 (some 1) (.ref 17)]

/-- `cancel-key = "Cancel-Key:" sp c-key-list crlf` (RFC 8315) -/
def rCancelKey : Term := .seq [.text "Cancel-Key:", .ref 148, .ref 20, .ref 37]

/-- `cancel-lock = "Cancel-Lock:" sp c-lock-list crlf` (RFC 8315) -/
def rCancelLock : Term := .seq [.text "Cancel-Lock:", .ref 148, .ref 23, .ref 37]

/-- `cc = "Cc:" sp address-list crlf` (RFC 5322, with a space after the colon, as RFC 5536 §2.2
asks of every field) -/
def rCc : Term := .seq [.text "Cc:", .ref 148, .ref 2, .ref 37]

/-- `ccontent = ctext / quoted-pair / comment` (RFC 5322) -/
def rCcontent : Term := .alt [.ref 38, .ref 126, .ref 31]

/-- `cfws = 1*([fws] comment) [fws] / fws` (RFC 5322) -/
def rCfws : Term := .alt [.seq [.rep 1 none (.seq [.rep 0 (some 1) (.ref 72), .ref 31]), .rep 0
    (some 1) (.ref 72)], .ref 72]

/-- `charset = 1*attribute-char` (RFC 2231 §7) -/
def rCharset : Term := .rep 1 none (.ref 14)

/-- `comment = "(" *([fws] ccontent) [fws] ")"` (RFC 5322) -/
def rComment : Term := .seq [.text "(", .rep 0 none (.seq [.rep 0 (some 1) (.ref 72), .ref 28]),
    .rep 0 (some 1) (.ref 72), .text ")"]

/-- `comments = "Comments:" sp unstructured crlf` (RFC 5536) -/
def rComments : Term := .seq [.text "Comments:", .ref 148, .ref 158, .ref 37]

/-- `component = 1*component-char` (RFC 5536) -/
def rComponent : Term := .rep 1 none (.ref 34)

/-- `component-char = alpha / digit / "+" / "-" / "_"` (RFC 5536) -/
def rComponentChar : Term := .alt [.ref 3, .ref 50, .text "+", .text "-", .text "_"]

/-- `control = "Control:" sp *wsp control-command *wsp crlf` (RFC 5536) -/
def rControl : Term := .seq [.text "Control:", .ref 148, .rep 0 none (.ref 164), .ref 36, .rep 0
    none (.ref 164), .ref 37]

/-- `control-command = verb *(1*wsp argument)` (RFC 5536) -/
def rControlCommand : Term := .seq [.ref 162, .rep 0 none (.seq [.rep 1 none (.ref 164), .ref 9])]

/-- `crlf = %x0D.0A` (RFC 5234) -/
def rCrlf : Term := .exact [13, 10]

/-- `ctext = %x21-27 / %x2A-5B / %x5D-7E` (RFC 5322) -/
def rCtext : Term := .alt [.range 33 39, .range 42 91, .range 93 126]

/-- `date = day month year` (RFC 5322) -/
def rDate : Term := .seq [.ref 41, .ref 98, .ref 166]

/-- `date-time = [day-of-week ","] date time [cfws]` (RFC 5322) -/
def rDateTime : Term := .seq [.rep 0 (some 1) (.seq [.ref 43, .text ","]), .ref 39, .ref 153, .rep 0
    (some 1) (.ref 29)]

/-- `day = [fws] 1*2digit fws` (RFC 5322) -/
def rDay : Term := .seq [.rep 0 (some 1) (.ref 72), .rep 1 (some 2) (.ref 50), .ref 72]

/-- `day-name = "Mon" / "Tue" / "Wed" / "Thu" / "Fri" / "Sat" / "Sun"` (RFC 5322) -/
def rDayName : Term := .alt [.text "Mon", .text "Tue", .text "Wed", .text "Thu", .text "Fri", .text
    "Sat", .text "Sun"]

/-- `day-of-week = [fws] day-name` (RFC 5322) -/
def rDayOfWeek : Term := .seq [.rep 0 (some 1) (.ref 72), .ref 42]

/-- `dec-octet = digit / %x31-39 digit / "1" 2digit / "2" %x30-34 digit / "25" %x30-35` (RFC
3986) -/
def rDecOctet : Term := .alt [.ref 50, .seq [.range 49 57, .ref 50], .seq [.text "1", .rep 2 (some
    2) (.ref 50)], .seq [.text "2", .range 48 52, .ref 50], .seq [.text "25", .range 48 53]]

/-- `diag-deprecated = "!" ipv4address [fws]` (RFC 5536) -/
def rDiagDeprecated : Term := .seq [.text "!", .ref 84, .rep 0 (some 1) (.ref 72)]

/-- `diag-identity = path-identity / ipv4address / ipv6address` (RFC 5536) -/
def rDiagIdentity : Term := .alt [.ref 117, .ref 84, .ref 85]

/-- `diag-keyword = 1*alpha` (RFC 5536) -/
def rDiagKeyword : Term := .rep 1 none (.ref 3)

/-- `diag-match = "!"` (RFC 5536) -/
def rDiagMatch : Term := .text "!"

/-- `diag-other = "!." diag-keyword ["." diag-identity] [fws]` (RFC 5536) -/
def rDiagOther : Term := .seq [.text "!.", .ref 47, .rep 0 (some 1) (.seq [.text ".", .ref 46]),
    .rep 0 (some 1) (.ref 72)]

/-- `digit = %x30-39` (RFC 5234) -/
def rDigit : Term := .range 48 57

/-- `display-name = phrase` (RFC 5322) -/
def rDisplayName : Term := .ref 120

/-- `dist-list = *wsp dist-name *([fws] "," [fws] dist-name) *wsp` (RFC 5536) -/
def rDistList : Term := .seq [.rep 0 none (.ref 164), .ref 53, .rep 0 none (.seq [.rep 0 (some 1)
    (.ref 72), .text ",", .rep 0 (some 1) (.ref 72), .ref 53]), .rep 0 none (.ref 164)]

/-- `dist-name = (alpha / digit) *(alpha / digit / "+" / "-" / "_")` (RFC 5536 §3.2.4, grouped as
its text intends) -/
def rDistName : Term := .seq [.alt [.ref 3, .ref 50], .rep 0 none (.alt [.ref 3, .ref 50, .text "+",
    .text "-", .text "_"])]

/-- `distribution = "Distribution:" sp dist-list crlf` (RFC 5536) -/
def rDistribution : Term := .seq [.text "Distribution:", .ref 148, .ref 52, .ref 37]

/-- `domain = dot-atom / domain-literal` (RFC 5322) -/
def rDomain : Term := .alt [.ref 57, .ref 56]

/-- `domain-literal = [cfws] "[" *([fws] dtext) [fws] "]" [cfws]` (RFC 5322) -/
def rDomainLiteral : Term := .seq [.rep 0 (some 1) (.ref 29), .text "[", .rep 0 none (.seq [.rep 0
    (some 1) (.ref 72), .ref 60]), .rep 0 (some 1) (.ref 72), .text "]", .rep 0 (some 1) (.ref 29)]

/-- `dot-atom = [cfws] dot-atom-text [cfws]` (RFC 5322) -/
def rDotAtom : Term := .seq [.rep 0 (some 1) (.ref 29), .ref 58, .rep 0 (some 1) (.ref 29)]

/-- `dot-atom-text = 1*atext *("." 1*atext)` (RFC 5322) -/
def rDotAtomText : Term := .seq [.rep 1 none (.ref 11), .rep 0 none (.seq [.text ".", .rep 1 none
    (.ref 11)])]

/-- `dquote = %x22` (RFC 5234) -/
def rDquote : Term := .range 34 34

/-- `dtext = %x21-5A / %x5E-7E` (RFC 5322) -/
def rDtext : Term := .alt [.range 33 90, .range 94 126]

/-- `expires = "Expires:" sp date-time crlf` (RFC 5536) -/
def rExpires : Term := .seq [.text "Expires:", .ref 148, .ref 40, .ref 37]

/-- `ext-octet = "%" 2(digit / "A" / "B" / "C" / "D" / "E" / "F")` (RFC 2231 §7) -/
def rExtOctet : Term := .seq [.text "%", .rep 2 (some 2) (.alt [.ref 50, .text "A", .text "B", .text
    "C", .text "D", .text "E", .text "F"])]

/-- `extended-initial-name = attribute [initial-section] "*"` (RFC 2231 §7) -/
def rExtendedInitialName : Term := .seq [.ref 13, .rep 0 (some 1) (.ref 81), .text "*"]

/-- `extended-initial-value = [charset] "'" [language] "'" extended-other-values` (RFC 2231 §7) -/
def rExtendedInitialValue : Term := .seq [.rep 0 (some 1) (.ref 30), .text "'", .rep 0 (some 1)
    (.ref 88), .text "'", .ref 66]

/-- `extended-other-names = attribute other-sections "*"` (RFC 2231 §7) -/
def rExtendedOtherNames : Term := .seq [.ref 13, .ref 113, .text "*"]

/-- `extended-other-values = *(ext-octet / attribute-char)` (RFC 2231 §7) -/
def rExtendedOtherValues : Term := .rep 0 none (.alt [.ref 62, .ref 14])

/-- `extended-parameter = extended-initial-name [cfws] "=" [cfws] extended-initial-value [cfws] /
extended-other-names [cfws] "=" [cfws] extended-other-values [cfws]` (RFC 2231 §7, erratum 477,
with the CFWS of RFC 5536 §3.2.8) -/
def rExtendedParameter : Term := .alt [.seq [.ref 63, .rep 0 (some 1) (.ref 29), .text "=", .rep 0
    (some 1) (.ref 29), .ref 64, .rep 0 (some 1) (.ref 29)], .seq [.ref 65, .rep 0 (some 1) (.ref
    29), .text "=", .rep 0 (some 1) (.ref 29), .ref 66, .rep 0 (some 1) (.ref 29)]]

/-- `field-name = 1*ftext` (RFC 5322) -/
def rFieldName : Term := .rep 1 none (.ref 71)

/-- `followup-to = "Followup-To:" sp (newsgroup-list / poster-text) crlf` (RFC 5536) -/
def rFollowupTo : Term := .seq [.text "Followup-To:", .ref 148, .alt [.ref 102, .ref 121], .ref 37]

/-- `from = "From:" sp mailbox-list crlf` (RFC 5536) -/
def rFrom : Term := .seq [.text "From:", .ref 148, .ref 94, .ref 37]

/-- `ftext = %x21-39 / %x3B-7E` (RFC 5322) -/
def rFtext : Term := .alt [.range 33 57, .range 59 126]

/-- `fws = [*wsp crlf] 1*wsp` (RFC 5322) -/
def rFws : Term := .seq [.rep 0 (some 1) (.seq [.rep 0 none (.ref 164), .ref 37]), .rep 1 none (.ref
    164)]

/-- `group = display-name ":" [group-list] ";" [cfws]` (RFC 5322) -/
def rGroup : Term := .seq [.ref 51, .text ":", .rep 0 (some 1) (.ref 74), .text ";", .rep 0 (some 1)
    (.ref 29)]

/-- `group-list = mailbox-list / cfws` (RFC 5322) -/
def rGroupList : Term := .alt [.ref 94, .ref 29]

/-- `h16 = 1*4hexdig` (RFC 3986) -/
def rH16 : Term := .rep 1 (some 4) (.ref 76)

/-- `hexdig = digit / "A" / "B" / "C" / "D" / "E" / "F"` (RFC 5234) -/
def rHexdig : Term := .alt [.ref 50, .text "A", .text "B", .text "C", .text "D", .text "E", .text
    "F"]

/-- `hour = 2digit` (RFC 5322) -/
def rHour : Term := .rep 2 (some 2) (.ref 50)

/-- `htab = %x09` (RFC 5234) -/
def rHtab : Term := .range 9 9

/-- `id-left = dot-atom-text` (RFC 5536) -/
def rIdLeft : Term := .ref 58

/-- `id-right = dot-atom-text / no-fold-literal` (RFC 5536) -/
def rIdRight : Term := .alt [.ref 58, .ref 105]

/-- `initial-section = "*0"` (RFC 2231 §7) -/
def rInitialSection : Term := .text "*0"

/-- `injection-date = "Injection-Date:" sp date-time crlf` (RFC 5536) -/
def rInjectionDate : Term := .seq [.text "Injection-Date:", .ref 148, .ref 40, .ref 37]

/-- `injection-info = "Injection-Info:" sp [cfws] path-identity [cfws] *(";" [cfws] parameter)
[cfws] crlf` (RFC 5536) -/
def rInjectionInfo : Term := .seq [.text "Injection-Info:", .ref 148, .rep 0 (some 1) (.ref 29),
    .ref 117, .rep 0 (some 1) (.ref 29), .rep 0 none (.seq [.text ";", .rep 0 (some 1) (.ref 29),
    .ref 114]), .rep 0 (some 1) (.ref 29), .ref 37]

/-- `ipv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet` (RFC 3986) -/
def rIpv4address : Term := .seq [.ref 44, .text ".", .ref 44, .text ".", .ref 44, .text ".", .ref
    44]

/-- `ipv6address = 6(h16 ":") ls32 / "::" 5(h16 ":") ls32 / [h16] "::" 4(h16 ":") ls32 / [[h16
":"] h16] "::" 3(h16 ":") ls32 / [*2(h16 ":") h16] "::" 2(h16 ":") ls32 / [*3(h16 ":") h16] "::"
h16 ":" ls32 / [*4(h16 ":") h16] "::" ls32 / [*5(h16 ":") h16] "::" h16 / [*6(h16 ":") h16] "::"`
(RFC 3986) -/
def rIpv6address : Term := .alt [.seq [.rep 6 (some 6) (.seq [.ref 75, .text ":"]), .ref 92], .seq
    [.text "::", .rep 5 (some 5) (.seq [.ref 75, .text ":"]), .ref 92], .seq [.rep 0 (some 1) (.ref
    75), .text "::", .rep 4 (some 4) (.seq [.ref 75, .text ":"]), .ref 92], .seq [.rep 0 (some 1)
    (.seq [.rep 0 (some 1) (.seq [.ref 75, .text ":"]), .ref 75]), .text "::", .rep 3 (some 3) (.seq
    [.ref 75, .text ":"]), .ref 92], .seq [.rep 0 (some 1) (.seq [.rep 0 (some 2) (.seq [.ref 75,
    .text ":"]), .ref 75]), .text "::", .rep 2 (some 2) (.seq [.ref 75, .text ":"]), .ref 92], .seq
    [.rep 0 (some 1) (.seq [.rep 0 (some 3) (.seq [.ref 75, .text ":"]), .ref 75]), .text "::", .ref
    75, .text ":", .ref 92], .seq [.rep 0 (some 1) (.seq [.rep 0 (some 4) (.seq [.ref 75, .text
    ":"]), .ref 75]), .text "::", .ref 92], .seq [.rep 0 (some 1) (.seq [.rep 0 (some 5) (.seq [.ref
    75, .text ":"]), .ref 75]), .text "::", .ref 75], .seq [.rep 0 (some 1) (.seq [.rep 0 (some 6)
    (.seq [.ref 75, .text ":"]), .ref 75]), .text "::"]]

/-- `keywords = "Keywords:" sp phrase *("," phrase) crlf` (RFC 5536) -/
def rKeywords : Term := .seq [.text "Keywords:", .ref 148, .ref 120, .rep 0 none (.seq [.text ",",
    .ref 120]), .ref 37]

/-- `label = alphanum [*(alphanum / "-") alphanum]` (RFC 5536) -/
def rLabel : Term := .seq [.ref 4, .rep 0 (some 1) (.seq [.rep 0 none (.alt [.ref 4, .text "-"]),
    .ref 4])]

/-- `language = 1*(alpha / digit / "-")` (RFC 2231 §7) -/
def rLanguage : Term := .rep 1 none (.alt [.ref 3, .ref 50, .text "-"])

/-- `lines = "Lines:" sp *wsp 1*digit *wsp crlf` (RFC 5536) -/
def rLines : Term := .seq [.text "Lines:", .ref 148, .rep 0 none (.ref 164), .rep 1 none (.ref 50),
    .rep 0 none (.ref 164), .ref 37]

/-- `local-part = dot-atom / quoted-string` (RFC 5322) -/
def rLocalPart : Term := .alt [.ref 57, .ref 127]

/-- `location = newsgroup-name ":" article-locator` (RFC 5536) -/
def rLocation : Term := .seq [.ref 103, .text ":", .ref 10]

/-- `ls32 = h16 ":" h16 / ipv4address` (RFC 3986) -/
def rLs32 : Term := .alt [.seq [.ref 75, .text ":", .ref 75], .ref 84]

/-- `mailbox = name-addr / addr-spec` (RFC 5322) -/
def rMailbox : Term := .alt [.ref 101, .ref 0]

/-- `mailbox-list = mailbox *("," mailbox)` (RFC 5322) -/
def rMailboxList : Term := .seq [.ref 93, .rep 0 none (.seq [.text ",", .ref 93])]

/-- `mdtext = %x21-3D / %x3F-5A / %x5E-7E` (RFC 5536) -/
def rMdtext : Term := .alt [.range 33 61, .range 63 90, .range 94 126]

/-- `message-id = "Message-ID:" sp *wsp msg-id *wsp crlf` (RFC 5536) -/
def rMessageId : Term := .seq [.text "Message-ID:", .ref 148, .rep 0 none (.ref 164), .ref 99, .rep
    0 none (.ref 164), .ref 37]

/-- `minute = 2digit` (RFC 5322) -/
def rMinute : Term := .rep 2 (some 2) (.ref 50)

/-- `month = "Jan" / "Feb" / "Mar" / "Apr" / "May" / "Jun" / "Jul" / "Aug" / "Sep" / "Oct" /
"Nov" / "Dec"` (RFC 5322) -/
def rMonth : Term := .alt [.text "Jan", .text "Feb", .text "Mar", .text "Apr", .text "May", .text
    "Jun", .text "Jul", .text "Aug", .text "Sep", .text "Oct", .text "Nov", .text "Dec"]

/-- `msg-id = "<" msg-id-core ">"` (RFC 5536) -/
def rMsgId : Term := .seq [.text "<", .ref 100, .text ">"]

/-- `msg-id-core = id-left "@" id-right` (RFC 5536) -/
def rMsgIdCore : Term := .seq [.ref 79, .text "@", .ref 80]

/-- `name-addr = [display-name] angle-addr` (RFC 5322) -/
def rNameAddr : Term := .seq [.rep 0 (some 1) (.ref 51), .ref 5]

/-- `newsgroup-list = *wsp newsgroup-name *([fws] "," [fws] newsgroup-name) *wsp` (RFC 5536) -/
def rNewsgroupList : Term := .seq [.rep 0 none (.ref 164), .ref 103, .rep 0 none (.seq [.rep 0 (some
    1) (.ref 72), .text ",", .rep 0 (some 1) (.ref 72), .ref 103]), .rep 0 none (.ref 164)]

/-- `newsgroup-name = component *("." component)` (RFC 5536) -/
def rNewsgroupName : Term := .seq [.ref 33, .rep 0 none (.seq [.text ".", .ref 33])]

/-- `newsgroups = "Newsgroups:" sp newsgroup-list crlf` (RFC 5536) -/
def rNewsgroups : Term := .seq [.text "Newsgroups:", .ref 148, .ref 102, .ref 37]

/-- `no-fold-literal = "[" *mdtext "]"` (RFC 5536) -/
def rNoFoldLiteral : Term := .seq [.text "[", .rep 0 none (.ref 95), .text "]"]

/-- `obs-c-key-string = 1*base64-octet` (RFC 8315) -/
def rObsCKeyString : Term := .rep 1 none (.ref 16)

/-- `obs-phrase = word *(word / "." / cfws)` (RFC 5322) -/
def rObsPhrase : Term := .seq [.ref 163, .rep 0 none (.alt [.ref 163, .text ".", .ref 29])]

/-- `obs-scheme = "sha1"` (RFC 8315) -/
def rObsScheme : Term := .text "sha1"

/-- `obs-zone = "GMT"` (RFC 5536 §2.1, §3.1.1) -/
def rObsZone : Term := .text "GMT"

/-- `optional-field = field-name ":" sp unstructured crlf` (RFC 5322, with a space after the
colon, as RFC 5536 §2.2 asks of every field) -/
def rOptionalField : Term := .seq [.ref 68, .text ":", .ref 148, .ref 158, .ref 37]

/-- `organization = "Organization:" sp unstructured crlf` (RFC 5536) -/
def rOrganization : Term := .seq [.text "Organization:", .ref 148, .ref 158, .ref 37]

/-- `orig-date = "Date:" sp date-time crlf` (RFC 5536) -/
def rOrigDate : Term := .seq [.text "Date:", .ref 148, .ref 40, .ref 37]

/-- `other-sections = "*" %x31-39 *digit` (RFC 2231 §7, erratum 7326) -/
def rOtherSections : Term := .seq [.text "*", .range 49 57, .rep 0 none (.ref 50)]

/-- `parameter = regular-parameter / extended-parameter` (RFC 2231 §7) -/
def rParameter : Term := .alt [.ref 131, .ref 67]

/-- `path = "Path:" sp *wsp path-list tail-entry *wsp crlf` (RFC 5536) -/
def rPath : Term := .seq [.text "Path:", .ref 148, .rep 0 none (.ref 164), .ref 118, .ref 152, .rep
    0 none (.ref 164), .ref 37]

/-- `path-diagnostic = diag-match / diag-other / diag-deprecated` (RFC 5536) -/
def rPathDiagnostic : Term := .alt [.ref 48, .ref 49, .ref 45]

/-- `path-identity = 1*(label ".") toplabel / path-nodot` (RFC 5536) -/
def rPathIdentity : Term := .alt [.seq [.rep 1 none (.seq [.ref 87, .text "."]), .ref 157], .ref
    119]

/-- `path-list = *(path-identity [fws] [path-diagnostic] "!")` (RFC 5536) -/
def rPathList : Term := .rep 0 none (.seq [.ref 117, .rep 0 (some 1) (.ref 72), .rep 0 (some 1)
    (.ref 116), .text "!"])

/-- `path-nodot = 1*(alphanum / "-" / "_")` (RFC 5536) -/
def rPathNodot : Term := .rep 1 none (.alt [.ref 4, .text "-", .text "_"])

/-- `phrase = 1*word / obs-phrase` (RFC 5322) -/
def rPhrase : Term := .alt [.rep 1 none (.ref 163), .ref 107]

/-- `poster-text = *wsp %x70.6F.73.74.65.72 *wsp` (RFC 5536) -/
def rPosterText : Term := .seq [.rep 0 none (.ref 164), .exact [112, 111, 115, 116, 101, 114], .rep
    0 none (.ref 164)]

/-- `product = [cfws] token [[cfws] "/" product-version]` (RFC 5536) -/
def rProduct : Term := .seq [.rep 0 (some 1) (.ref 29), .ref 156, .rep 0 (some 1) (.seq [.rep 0
    (some 1) (.ref 29), .text "/", .ref 123])]

/-- `product-version = [cfws] token` (RFC 5536) -/
def rProductVersion : Term := .seq [.rep 0 (some 1) (.ref 29), .ref 156]

/-- `qcontent = qtext / quoted-pair` (RFC 5322) -/
def rQcontent : Term := .alt [.ref 125, .ref 126]

/-- `qtext = %x21 / %x23-5B / %x5D-7E` (RFC 5322) -/
def rQtext : Term := .alt [.range 33 33, .range 35 91, .range 93 126]

/-- `quoted-pair = "\" (vchar / wsp)` (RFC 5322) -/
def rQuotedPair : Term := .seq [.text "\\", .alt [.ref 161, .ref 164]]

/-- `quoted-string = [cfws] dquote *([fws] qcontent) [fws] dquote [cfws]` (RFC 5322) -/
def rQuotedString : Term := .seq [.rep 0 (some 1) (.ref 29), .ref 59, .rep 0 none (.seq [.rep 0
    (some 1) (.ref 72), .ref 124]), .rep 0 (some 1) (.ref 72), .ref 59, .rep 0 (some 1) (.ref 29)]

/-- `received = "Received:" sp [1*received-token / cfws] ";" date-time crlf` (RFC 5322, erratum
3979, with a space after the colon, as RFC 5536 §2.2 asks of every field) -/
def rReceived : Term := .seq [.text "Received:", .ref 148, .rep 0 (some 1) (.alt [.rep 1 none (.ref
    129), .ref 29]), .text ";", .ref 40, .ref 37]

/-- `received-token = word / angle-addr / addr-spec / domain` (RFC 5322) -/
def rReceivedToken : Term := .alt [.ref 163, .ref 5, .ref 0, .ref 55]

/-- `references = "References:" sp [cfws] msg-id *(cfws msg-id) [cfws] crlf` (RFC 5536) -/
def rReferences : Term := .seq [.text "References:", .ref 148, .rep 0 (some 1) (.ref 29), .ref 99,
    .rep 0 none (.seq [.ref 29, .ref 99]), .rep 0 (some 1) (.ref 29), .ref 37]

/-- `regular-parameter = regular-parameter-name [cfws] "=" [cfws] value [cfws]` (RFC 2231 §7,
with the CFWS of RFC 5536 §3.2.8) -/
def rRegularParameter : Term := .seq [.ref 132, .rep 0 (some 1) (.ref 29), .text "=", .rep 0 (some
    1) (.ref 29), .ref 160, .rep 0 (some 1) (.ref 29)]

/-- `regular-parameter-name = attribute [section]` (RFC 2231 §7) -/
def rRegularParameterName : Term := .seq [.ref 13, .rep 0 (some 1) (.ref 145)]

/-- `reply-to = "Reply-To:" sp address-list crlf` (RFC 5536) -/
def rReplyTo : Term := .seq [.text "Reply-To:", .ref 148, .ref 2, .ref 37]

/-- `resent-bcc = "Resent-Bcc:" sp [address-list / cfws] crlf` (RFC 5322, with a space after the
colon, as RFC 5536 §2.2 asks of every field) -/
def rResentBcc : Term := .seq [.text "Resent-Bcc:", .ref 148, .rep 0 (some 1) (.alt [.ref 2, .ref
    29]), .ref 37]

/-- `resent-cc = "Resent-Cc:" sp address-list crlf` (RFC 5322, with a space after the colon, as
RFC 5536 §2.2 asks of every field) -/
def rResentCc : Term := .seq [.text "Resent-Cc:", .ref 148, .ref 2, .ref 37]

/-- `resent-date = "Resent-Date:" sp date-time crlf` (RFC 5322, with a space after the colon, as
RFC 5536 §2.2 asks of every field) -/
def rResentDate : Term := .seq [.text "Resent-Date:", .ref 148, .ref 40, .ref 37]

/-- `resent-from = "Resent-From:" sp mailbox-list crlf` (RFC 5322, with a space after the colon,
as RFC 5536 §2.2 asks of every field) -/
def rResentFrom : Term := .seq [.text "Resent-From:", .ref 148, .ref 94, .ref 37]

/-- `resent-sender = "Resent-Sender:" sp mailbox crlf` (RFC 5322, with a space after the colon,
as RFC 5536 §2.2 asks of every field) -/
def rResentSender : Term := .seq [.text "Resent-Sender:", .ref 148, .ref 93, .ref 37]

/-- `resent-to = "Resent-To:" sp address-list crlf` (RFC 5322, with a space after the colon, as
RFC 5536 §2.2 asks of every field) -/
def rResentTo : Term := .seq [.text "Resent-To:", .ref 148, .ref 2, .ref 37]

/-- `return = "Return-Path:" sp return-path-address crlf` (RFC 5322, with a space after the
colon, as RFC 5536 §2.2 asks of every field) -/
def rReturn : Term := .seq [.text "Return-Path:", .ref 148, .ref 141, .ref 37]

/-- `return-path-address = angle-addr / [cfws] "<" [cfws] ">" [cfws]` (RFC 5322, renamed) -/
def rReturnPathAddress : Term := .alt [.ref 5, .seq [.rep 0 (some 1) (.ref 29), .text "<", .rep 0
    (some 1) (.ref 29), .text ">", .rep 0 (some 1) (.ref 29)]]

/-- `scheme = "sha256" / "sha512" / 1*scheme-char / obs-scheme` (RFC 8315) -/
def rScheme : Term := .alt [.text "sha256", .text "sha512", .rep 1 none (.ref 143), .ref 108]

/-- `scheme-char = alpha / digit / "-" / "/"` (RFC 8315) -/
def rSchemeChar : Term := .alt [.ref 3, .ref 50, .text "-", .text "/"]

/-- `second = 2digit` (RFC 5322) -/
def rSecond : Term := .rep 2 (some 2) (.ref 50)

/-- `section = initial-section / other-sections` (RFC 2231 §7) -/
def rSection : Term := .alt [.ref 81, .ref 113]

/-- `sender = "Sender:" sp mailbox crlf` (RFC 5536) -/
def rSender : Term := .seq [.text "Sender:", .ref 148, .ref 93, .ref 37]

/-- `server-name = path-identity` (RFC 5536) -/
def rServerName : Term := .ref 117

/-- `sp = %x20` (RFC 5234) -/
def rSp : Term := .range 32 32

/-- `subject = "Subject:" sp unstructured crlf` (RFC 5536) -/
def rSubject : Term := .seq [.text "Subject:", .ref 148, .ref 158, .ref 37]

/-- `summary = "Summary:" sp unstructured crlf` (RFC 5536) -/
def rSummary : Term := .seq [.text "Summary:", .ref 148, .ref 158, .ref 37]

/-- `supersedes = "Supersedes:" sp *wsp msg-id *wsp crlf` (RFC 5536) -/
def rSupersedes : Term := .seq [.text "Supersedes:", .ref 148, .rep 0 none (.ref 164), .ref 99, .rep
    0 none (.ref 164), .ref 37]

/-- `tail-entry = path-nodot` (RFC 5536) -/
def rTailEntry : Term := .ref 119

/-- `time = time-of-day zone` (RFC 5322) -/
def rTime : Term := .seq [.ref 154, .ref 167]

/-- `time-of-day = hour ":" minute [":" second]` (RFC 5322) -/
def rTimeOfDay : Term := .seq [.ref 77, .text ":", .ref 97, .rep 0 (some 1) (.seq [.text ":", .ref
    144])]

/-- `to = "To:" sp address-list crlf` (RFC 5322, with a space after the colon, as RFC 5536 §2.2
asks of every field) -/
def rTo : Term := .seq [.text "To:", .ref 148, .ref 2, .ref 37]

/-- `token = 1*(%x21 / %x23-27 / %x2A-2B / %x2D-2E / %x30-39 / %x41-5A / %x5E-7E)` (RFC 2045
§5.1, erratum 512) -/
def rToken : Term := .rep 1 none (.alt [.range 33 33, .range 35 39, .range 42 43, .range 45 46,
    .range 48 57, .range 65 90, .range 94 126])

/-- `toplabel = [label *"-"] alpha *"-" label / label *"-" alpha [*"-" label] / label 1*"-"
label` (RFC 5536) -/
def rToplabel : Term := .alt [.seq [.rep 0 (some 1) (.seq [.ref 87, .rep 0 none (.text "-")]), .ref
    3, .rep 0 none (.text "-"), .ref 87], .seq [.ref 87, .rep 0 none (.text "-"), .ref 3, .rep 0
    (some 1) (.seq [.rep 0 none (.text "-"), .ref 87])], .seq [.ref 87, .rep 1 none (.text "-"),
    .ref 87]]

/-- `unstructured = *wsp vchar *([fws] vchar) *wsp` (RFC 5536) -/
def rUnstructured : Term := .seq [.rep 0 none (.ref 164), .ref 161, .rep 0 none (.seq [.rep 0 (some
    1) (.ref 72), .ref 161]), .rep 0 none (.ref 164)]

/-- `user-agent = "User-Agent:" sp 1*product [cfws] crlf` (RFC 5536) -/
def rUserAgent : Term := .seq [.text "User-Agent:", .ref 148, .rep 1 none (.ref 122), .rep 0 (some
    1) (.ref 29), .ref 37]

/-- `value = token / quoted-string` (RFC 2045 §5.1) -/
def rValue : Term := .alt [.ref 156, .ref 127]

/-- `vchar = %x21-7E` (RFC 5234) -/
def rVchar : Term := .range 33 126

/-- `verb = token` (RFC 5536) -/
def rVerb : Term := .ref 156

/-- `word = atom / quoted-string` (RFC 5322) -/
def rWord : Term := .alt [.ref 12, .ref 127]

/-- `wsp = sp / htab` (RFC 5234) -/
def rWsp : Term := .alt [.ref 148, .ref 78]

/-- `xref = "Xref:" sp *wsp server-name 1*(fws location) *wsp crlf` (RFC 5536) -/
def rXref : Term := .seq [.text "Xref:", .ref 148, .rep 0 none (.ref 164), .ref 147, .rep 1 none
    (.seq [.ref 72, .ref 91]), .rep 0 none (.ref 164), .ref 37]

/-- `year = fws 4*digit fws` (RFC 5322) -/
def rYear : Term := .seq [.ref 72, .rep 4 none (.ref 50), .ref 72]

/-- `zone = fws ("+" / "-") 4digit / [fws] obs-zone` (RFC 5322, erratum 6639) -/
def rZone : Term := .alt [.seq [.ref 72, .alt [.text "+", .text "-"], .rep 4 (some 4) (.ref 50)],
    .seq [.rep 0 (some 1) (.ref 72), .ref 109]]

/-- The rules, in the order of their names. -/
def grammar : Array Term := #[rAddrSpec, rAddress, rAddressList, rAlpha, rAlphanum, rAngleAddr,
  rApproved, rArchive, rArchiveParam, rArgument, rArticleLocator, rAtext, rAtom, rAttribute,
  rAttributeChar, rBase64Char, rBase64Octet, rBase64Terminal, rBcc, rCKey, rCKeyList, rCKeyString,
  rCLock, rCLockList, rCLockString, rCancelKey, rCancelLock, rCc, rCcontent, rCfws, rCharset,
  rComment, rComments, rComponent, rComponentChar, rControl, rControlCommand, rCrlf, rCtext, rDate,
  rDateTime, rDay, rDayName, rDayOfWeek, rDecOctet, rDiagDeprecated, rDiagIdentity, rDiagKeyword,
  rDiagMatch, rDiagOther, rDigit, rDisplayName, rDistList, rDistName, rDistribution, rDomain,
  rDomainLiteral, rDotAtom, rDotAtomText, rDquote, rDtext, rExpires, rExtOctet,
  rExtendedInitialName, rExtendedInitialValue, rExtendedOtherNames, rExtendedOtherValues,
  rExtendedParameter, rFieldName, rFollowupTo, rFrom, rFtext, rFws, rGroup, rGroupList, rH16,
  rHexdig, rHour, rHtab, rIdLeft, rIdRight, rInitialSection, rInjectionDate, rInjectionInfo,
  rIpv4address, rIpv6address, rKeywords, rLabel, rLanguage, rLines, rLocalPart, rLocation, rLs32,
  rMailbox, rMailboxList, rMdtext, rMessageId, rMinute, rMonth, rMsgId, rMsgIdCore, rNameAddr,
  rNewsgroupList, rNewsgroupName, rNewsgroups, rNoFoldLiteral, rObsCKeyString, rObsPhrase,
  rObsScheme, rObsZone, rOptionalField, rOrganization, rOrigDate, rOtherSections, rParameter, rPath,
  rPathDiagnostic, rPathIdentity, rPathList, rPathNodot, rPhrase, rPosterText, rProduct,
  rProductVersion, rQcontent, rQtext, rQuotedPair, rQuotedString, rReceived, rReceivedToken,
  rReferences, rRegularParameter, rRegularParameterName, rReplyTo, rResentBcc, rResentCc,
  rResentDate, rResentFrom, rResentSender, rResentTo, rReturn, rReturnPathAddress, rScheme,
  rSchemeChar, rSecond, rSection, rSender, rServerName, rSp, rSubject, rSummary, rSupersedes,
  rTailEntry, rTime, rTimeOfDay, rTo, rToken, rToplabel, rUnstructured, rUserAgent, rValue, rVchar,
  rVerb, rWord, rWsp, rXref, rYear, rZone]

/-- The rules' names, as the RFCs write them in lower case. -/
def names : Array String := #["addr-spec", "address", "address-list", "alpha", "alphanum",
  "angle-addr", "approved", "archive", "archive-param", "argument", "article-locator", "atext",
  "atom", "attribute", "attribute-char", "base64-char", "base64-octet", "base64-terminal", "bcc",
  "c-key", "c-key-list", "c-key-string", "c-lock", "c-lock-list", "c-lock-string", "cancel-key",
  "cancel-lock", "cc", "ccontent", "cfws", "charset", "comment", "comments", "component",
  "component-char", "control", "control-command", "crlf", "ctext", "date", "date-time", "day",
  "day-name", "day-of-week", "dec-octet", "diag-deprecated", "diag-identity", "diag-keyword",
  "diag-match", "diag-other", "digit", "display-name", "dist-list", "dist-name", "distribution",
  "domain", "domain-literal", "dot-atom", "dot-atom-text", "dquote", "dtext", "expires",
  "ext-octet", "extended-initial-name", "extended-initial-value", "extended-other-names",
  "extended-other-values", "extended-parameter", "field-name", "followup-to", "from", "ftext",
  "fws", "group", "group-list", "h16", "hexdig", "hour", "htab", "id-left", "id-right",
  "initial-section", "injection-date", "injection-info", "ipv4address", "ipv6address", "keywords",
  "label", "language", "lines", "local-part", "location", "ls32", "mailbox", "mailbox-list",
  "mdtext", "message-id", "minute", "month", "msg-id", "msg-id-core", "name-addr", "newsgroup-list",
  "newsgroup-name", "newsgroups", "no-fold-literal", "obs-c-key-string", "obs-phrase", "obs-scheme",
  "obs-zone", "optional-field", "organization", "orig-date", "other-sections", "parameter", "path",
  "path-diagnostic", "path-identity", "path-list", "path-nodot", "phrase", "poster-text", "product",
  "product-version", "qcontent", "qtext", "quoted-pair", "quoted-string", "received",
  "received-token", "references", "regular-parameter", "regular-parameter-name", "reply-to",
  "resent-bcc", "resent-cc", "resent-date", "resent-from", "resent-sender", "resent-to", "return",
  "return-path-address", "scheme", "scheme-char", "second", "section", "sender", "server-name",
  "sp", "subject", "summary", "supersedes", "tail-entry", "time", "time-of-day", "to", "token",
  "toplabel", "unstructured", "user-agent", "value", "vchar", "verb", "word", "wsp", "xref", "year",
  "zone"]

/-- The rule each field is checked by, by the field's name, and the rule for any other. -/
def fieldRules : List (String × Nat) := [("Date", 112), ("From", 70), ("Message-ID", 96),
  ("Newsgroups", 104), ("Path", 115), ("Subject", 149), ("Comments", 32), ("Keywords", 86),
  ("Reply-To", 133), ("Sender", 146), ("Approved", 6), ("Archive", 7), ("Control", 35),
  ("Distribution", 54), ("Expires", 61), ("Followup-To", 69), ("Injection-Date", 82),
  ("Injection-Info", 83), ("Organization", 111), ("References", 130), ("Summary", 150),
  ("Supersedes", 151), ("User-Agent", 159), ("Xref", 165), ("Lines", 89), ("Cancel-Lock", 26),
  ("Cancel-Key", 25), ("To", 155), ("Cc", 27), ("Bcc", 18), ("Resent-Date", 136), ("Resent-From",
  137), ("Resent-Sender", 138), ("Resent-To", 139), ("Resent-Cc", 135), ("Resent-Bcc", 134),
  ("Return-Path", 140), ("Received", 128)]

def optionalField : Nat := 110

/-- The most terms a match of this grammar goes through, one inside the next, at one position of
its input: the grammar has no left recursion, and `scripts/gen_abnf.py` counts them
(`DN.News.Abnf.fuel`). -/
def depth : Nat := 36

end DN.News.AbnfRules
