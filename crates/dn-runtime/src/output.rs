/// A completion larger than the submitted remainder is an adapter error: the
/// kernel cannot have sent bytes that were never handed to it.
#[derive(Debug, PartialEq, Eq)]
pub struct OverCompletion;

impl std::fmt::Display for OverCompletion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("completion reported more bytes than were submitted")
    }
}

impl std::error::Error for OverCompletion {}

/// Retains the source borrow until all bytes have been sent. No copy or allocation.
#[derive(Debug)]
pub struct OutputCursor<'a> {
    bytes: &'a [u8],
    sent: usize,
}

impl<'a> OutputCursor<'a> {
    /// A cursor over `bytes`, with nothing sent yet.
    #[must_use]
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, sent: 0 }
    }

    /// The bytes still to send.
    #[must_use]
    pub fn remaining(&self) -> &'a [u8] {
        &self.bytes[self.sent..]
    }

    /// How many bytes have been reported sent.
    #[must_use]
    pub fn sent(&self) -> usize {
        self.sent
    }

    /// `true` once every byte has been reported sent.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.sent == self.bytes.len()
    }

    /// Report `count` bytes sent.
    ///
    /// A zero completion leaves the cursor unchanged. The adapter must handle
    /// closed sockets / backpressure and must not busy-loop on zero progress.
    /// A count above the remainder is rejected and the cursor is untouched —
    /// the Lean model of the send path makes the same choice, so an adapter
    /// that over-reports is an error on both sides rather than a silent
    /// truncation.
    pub fn complete(&mut self, count: usize) -> Result<(), OverCompletion> {
        if count > self.bytes.len() - self.sent {
            return Err(OverCompletion);
        }
        self.sent += count;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn every_two_part_send_preserves_exact_bytes() {
        let bytes = b"220 article follows\r\n..hello\r\n.\r\n";
        for split in 0..=bytes.len() {
            let mut cursor = OutputCursor::new(bytes);
            assert_eq!(cursor.complete(bytes.len() + 1), Err(OverCompletion));
            assert_eq!(cursor.remaining(), bytes);
            assert_eq!(cursor.sent(), 0);
            cursor.complete(split).unwrap();
            assert_eq!(cursor.remaining(), &bytes[split..]);
            assert_eq!(cursor.sent(), split);
            // One byte past the remainder is rejected, and the rejection leaves
            // the cursor where it was.
            assert_eq!(
                cursor.complete(bytes.len() - split + 1),
                Err(OverCompletion)
            );
            assert_eq!(cursor.sent(), split);
            cursor.complete(0).unwrap();
            cursor.complete(bytes.len() - split).unwrap();
            assert!(cursor.is_complete());
            assert_eq!(cursor.remaining(), b"");
            // Nothing more fits once the cursor is complete.
            assert_eq!(cursor.complete(1), Err(OverCompletion));
        }
    }

    #[test]
    fn empty_output_is_complete_from_the_start() {
        let mut cursor = OutputCursor::new(b"");
        assert!(cursor.is_complete());
        assert_eq!(cursor.remaining(), b"");
        cursor.complete(0).unwrap();
        assert_eq!(cursor.complete(1), Err(OverCompletion));
    }
}
