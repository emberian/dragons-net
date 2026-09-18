/// A completion larger than the submitted remainder is an adapter error.
#[derive(Debug, PartialEq, Eq)]
pub struct OverCompletion;

/// Retains the source borrow until all bytes have been sent. No copy or allocation.
pub struct OutputCursor<'a> {
    bytes: &'a [u8],
    sent: usize,
}

impl<'a> OutputCursor<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, sent: 0 }
    }
    pub fn remaining(&self) -> &'a [u8] {
        &self.bytes[self.sent..]
    }
    pub fn is_complete(&self) -> bool {
        self.sent == self.bytes.len()
    }

    /// A zero completion leaves the cursor unchanged. The adapter must handle
    /// closed sockets / backpressure and must not busy-loop on zero progress.
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
            cursor.complete(split).unwrap();
            assert_eq!(cursor.remaining(), &bytes[split..]);
            cursor.complete(0).unwrap();
            cursor.complete(bytes.len() - split).unwrap();
            assert!(cursor.is_complete());
        }
    }
}
