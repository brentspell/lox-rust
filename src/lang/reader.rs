/*!
# Character/token reader helpers for parsing
*/

use std::collections::VecDeque;

use anyhow::{anyhow, bail, Result};

/**
This is a simple wrapper around an iterator trait that implements lookahead for an arbitrary
number of elements. The cursor can be advanced by calling `read`, and future elements can
be accessed by calling `peek`.
*/
pub struct LookaheadReader<T> {
    iter: Box<dyn Iterator<Item = Result<T>>>,
    lookahead: VecDeque<T>,
}

impl<T> LookaheadReader<T> {
    /**
    Creates a new lookahead reader from a boxed iterator over any type.

    # Arguments
    * `iter` - the iterator to attach

    # Returns
    The initialized reader.
    */
    pub fn new(iter: impl Iterator<Item = Result<T>> + 'static) -> Self {
        Self {
            iter: Box::new(iter),
            lookahead: VecDeque::new(),
        }
    }

    /**
    Consumes the current element from the stream and advances to the next element.

    # Returns
    The requested element if it was read successfully before the end of iteration, or an
    Err/None otherwise.
    */
    pub fn read(&mut self) -> Result<Option<T>> {
        self.lookahead
            .pop_front()
            .map(Ok)
            .or_else(|| self.iter.next())
            .transpose()
    }

    /**
    Peeks at a future element from the iterator.

    # Arguments
    * `ahead` - the number of elements to look ahead

    # Returns
    The requested element if it was read successfully before the end of iteration, or an
    Err/None otherwise.
    */
    pub fn peek(&mut self, ahead: usize) -> Result<Option<&T>> {
        while ahead >= self.lookahead.len() {
            match self.iter.next() {
                Some(Ok(t)) => self.lookahead.push_back(t),
                Some(Err(e)) => bail!(e),
                _ => break,
            }
        }
        self.lookahead.get(ahead).map(Ok).transpose()
    }
}

/**
This struct wraps a character reader, providing support for iterating over characters
from the underlying `Read` instance.
*/
pub struct CharReaderIterator {
    read: char_reader::CharReader<Box<dyn std::io::Read>>,
}

impl CharReaderIterator {
    /**
    Creates a new reader iterator.

    # Arguments
    * `read` - the read object to attach

    # Returns
    The initialized iterator.
    */
    pub fn new(read: impl std::io::Read + 'static) -> Self {
        CharReaderIterator {
            read: char_reader::CharReader::new(Box::new(read)),
        }
    }
}

impl Iterator for CharReaderIterator {
    type Item = Result<char>;

    fn next(&mut self) -> Option<Result<char>> {
        self.read.next_char().map_err(|e| anyhow!(e)).transpose()
    }
}
