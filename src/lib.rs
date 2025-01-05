//! A Rust library to interact with GPT / MBR partition tables.
//!
//! It provides a set of tools to interact with storage devices at the partition table level,
//! supporting both Master Boot Record (MBR) and GUID Partition Table (GPT) formats.
//!
//! The library is designed to make it easy to read, write, and manipulate partition tables
//! for a variety of use cases, such as bootloader development, disk management utilities, or
//! storage diagnostics.

#![no_std]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

#[macro_use]
extern crate static_assertions;

pub mod mbr;
pub use mbr::{Mbr, MbrInplace, MbrPartition};

pub mod gpt;
pub use gpt::{Gpt, GptHeader, GptPartition};

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "std")]
pub use std::io::Read as DiskRead;

#[cfg(feature = "std")]
pub use std::io::Write as DiskWrite;

#[cfg(feature = "std")]
pub use std::io::Seek as DiskSeek;

#[cfg(feature = "std")]
pub use std::io::SeekFrom;

/// A trait for reading data from a disk-like device.
///
/// # Errors
/// The `read` method returns a `Result` indicating the number of bytes successfully read or an error.
/// An error is represented as a unit type (`()`).
///
/// # Examples
///
/// ```rust
/// use fzpart::DiskRead;
///
/// struct MyDevice;
///
/// impl DiskRead for MyDevice {
///     fn read(&mut self, buf: &mut [u8]) -> Result<usize, ()> {
///         // Custom implementation for reading data
///         Ok(0) // Placeholder
///     }
/// }
/// ```
#[cfg(not(feature = "std"))]
pub trait DiskRead {
    /// Reads data from the disk device into the provided buffer.
    ///
    /// # Arguments
    ///
    /// - `buf`: A mutable slice to store the read data.
    ///
    /// # Returns
    ///
    /// - `Ok(usize)`: Number of bytes read.
    /// - `Err(())`: An error occurred during the read operation.
    fn read(&mut self, but: &mut [u8]) -> Result<usize, ()>;
}

/// A trait for writing data to a disk-like device.
///
/// # Errors
///
/// The `write` method returns a `Result` indicating the number of bytes successfully written or an error.
///
/// # Examples
///
/// ```rust
/// use fzpart::DiskWrite;
///
/// struct MyDevice;
///
/// impl DiskWrite for MyDevice {
///     fn write(&mut self, buf: &[u8]) -> Result<usize, ()> {
///         // Custom implementation for writing data
///         Ok(buf.len()) // Placeholder
///     }
/// }
/// ```
#[cfg(not(feature = "std"))]
pub trait DiskWrite {
    /// Writes data from the provided buffer.
    ///
    /// # Arguments
    ///
    /// - `buf`: A slice containing the data to be written.
    ///
    /// # Returns
    ///
    /// - `Ok(usize)`: Number of bytes written.
    /// - `Err(())`: An error occurred during the write operation.
    fn write(&mut self, but: &[u8]) -> Result<usize, ()>;
}

/// Defines possible seek operations for a disk-like device.
///
/// # Examples
///
/// ```rust
/// use fzpart::SeekFrom;
///
/// let seek_operation = SeekFrom::Start(1024);
/// ```
#[cfg(not(feature = "std"))]
pub enum SeekFrom {
    Start(u64),
    End(i64),
    Current(i64),
}

/// A trait for moving the read/write pointer within a disk-like device.
///
/// # Errors
///
/// The `seek` method returns a `Result` indicating the new position or an error.
///
/// # Examples
///
/// ```rust
/// use fzpart::{DiskSeek, SeekFrom};
///
/// struct MyDevice;
///
/// impl DiskSeek for MyDevice {
///     fn seek(&mut self, pos: SeekFrom) -> Result<u64, ()> {
///         // Custom implementation for seeking
///         Ok(0) // Placeholder
///     }
/// }
/// ```
#[cfg(not(feature = "std"))]
pub trait DiskSeek {
    /// Moves the read/write pointer to a new position.
    ///
    /// # Arguments
    ///
    /// - `pos`: The seek operation to perform, as defined by [`SeekFrom`].
    ///
    /// # Returns
    ///
    /// - `Ok(u64)`: The new position in the device.
    /// - `Err(())`: An error occurred during the seek operation.
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, ()>;
}
