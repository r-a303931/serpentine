// context.rs: defines what a context should look like and be able
// to do at a minimum as well as defaults for the local system
// Copyright (C) 2023 Andrew Rioux
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.

use std::{ffi::OsStr, fs::OpenOptions, hash::Hash, path::Path, sync::Arc};

use async_trait::async_trait;

use crate::{stdlib, Position};

use super::{error::RuntimeError, Environment};

/// Represents the file statistics for a file in *nix
pub struct VmLinuxFileStats {
    bit_field: Option<u8>,
    mode: u32,
    file_size: u64,
    mtime: i64,
}

impl VmLinuxFileStats {
    /// Used to create the bit_field attribute when creating
    /// a new VmLinuxFileStats struct
    ///
    /// Composed of attributes pulled from the extended attributes
    /// system on most filesystems
    pub fn create_bit_field(
        appendonly: bool,
        compressed: bool,
        immutable: bool,
        journaled: bool,
        nocompression: bool,
        noatime: bool,
        nocow: bool,
    ) -> u8 {
        (u8::from(appendonly) << 6)
            | (u8::from(compressed) << 5)
            | (u8::from(immutable) << 4)
            | (u8::from(journaled) << 3)
            | (u8::from(nocompression) << 2)
            | (u8::from(noatime) << 1)
            | u8::from(nocow)
    }

    pub fn new(bit_field: Option<u8>, mode: u32, file_size: u64, mtime: i64) -> Self {
        Self {
            bit_field,
            mode,
            file_size,
            mtime,
        }
    }

    /// Determines if the file or directory this represents
    /// is append only
    ///
    /// Because not all file systems support extended attributes,
    /// not all directory entries have a bit field
    pub fn appendonly(&self) -> Option<bool> {
        Some((self.bit_field? & 0x40) != 0)
    }

    /// Determines if the file or directory this represents
    /// is compressed
    ///
    /// Because not all file systems support extended attributes,
    /// not all directory entries have a bit field
    pub fn compressed(&self) -> Option<bool> {
        Some((self.bit_field? & 0x20) != 0)
    }

    /// Determines if the file or directory this represents
    /// is immutable
    ///
    /// Because not all file systems support extended attributes,
    /// not all directory entries have a bit field
    pub fn immutable(&self) -> Option<bool> {
        Some((self.bit_field? & 0x10) != 0)
    }

    /// Determines if the file or directory this represents
    /// is journaled
    ///
    /// Because not all file systems support extended attributes,
    /// not all directory entries have a bit field
    pub fn journaled(&self) -> Option<bool> {
        Some((self.bit_field? & 0x08) != 0)
    }

    /// Determines if the file or directory this represents
    /// explicitly does not allow compression
    ///
    /// Because not all file systems support extended attributes,
    /// not all directory entries have a bit field
    pub fn nocompression(&self) -> Option<bool> {
        Some((self.bit_field? & 0x04) != 0)
    }

    /// Determines if the file or directory this represents
    /// explicity does not record access time
    ///
    /// Because not all file systems support extended attributes,
    /// not all directory entries have a bit field
    pub fn noatime(&self) -> Option<bool> {
        Some((self.bit_field? & 0x02) != 0)
    }

    /// Determines if the file or directory this represents
    /// doesn't allow for copy on write semantics
    ///
    /// Because not all file systems support extended attributes,
    /// not all directory entries have a bit field
    pub fn nocow(&self) -> Option<bool> {
        Some((self.bit_field? & 0x01) != 0)
    }

    /// Returns the file permissions stored for this file
    pub fn mode(&self) -> u32 {
        self.mode
    }

    /// Returns the file size of this file
    pub fn file_size(&self) -> u64 {
        self.file_size
    }

    /// Returns the last set modified time
    pub fn mtime(&self) -> i64 {
        self.mtime
    }
}

/// Utility type used for working with the mode attribute on
/// *nix systems to allow for understanding the file permissions
/// in use
///
/// Used to generated bitmasks that can filter for details in
/// the mode attribute of a directory entry
///
/// # Examples
///
/// ```
/// // Generate a mask to check for whether or not the user can write,
/// // and groups can read
/// # use serpentine::vm::context::ModeTarget;
/// assert_eq!(0o240, (ModeTarget::User & ModeTarget::Write) | (ModeTarget::Group & ModeTarget::Read));
/// ```
pub enum ModeTarget {
    User,
    Group,
    Other,
    Read,
    Write,
    Execute,
}

impl ModeTarget {
    /// Generate a bitmask corresponding with the target specified
    pub fn bitmask(&self) -> u32 {
        match self {
            Self::User => 0o700,
            Self::Group => 0o070,
            Self::Other => 0o007,
            Self::Read => 0o444,
            Self::Write => 0o222,
            Self::Execute => 0o111,
        }
    }
}

impl std::ops::BitXor for ModeTarget {
    type Output = u32;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.bitmask() ^ rhs.bitmask()
    }
}

impl std::ops::BitOr for ModeTarget {
    type Output = u32;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.bitmask() | rhs.bitmask()
    }
}

impl std::ops::BitAnd for ModeTarget {
    type Output = u32;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.bitmask() & rhs.bitmask()
    }
}

/// Represents file statistics for a file in Windows
pub struct VmWindowsFileStats {
    write_time: u64,
    bit_field: u64,
    file_size: u64,
}

impl VmWindowsFileStats {
    /// Returns the last time this file was written to
    pub fn write_time(&self) -> u64 {
        self.write_time
    }

    /// The file size of this file or directory on disk
    pub fn file_size(&self) -> u64 {
        self.file_size
    }

    /// Whether or not this file or folder is read only
    ///
    /// Does not represent children if it is a directory
    pub fn readonly(&self) -> bool {
        (self.bit_field & 0x01) != 0
    }

    /// Whether or not this file or folder is hidden
    ///
    /// Does not represent children if it is a directory
    pub fn hidden(&self) -> bool {
        (self.bit_field & 0x02) != 0
    }

    /// Whether or not this file or folder is a system file
    ///
    /// Does not represent children if it is a directory
    pub fn system(&self) -> bool {
        (self.bit_field & 0x04) != 0
    }

    /// Whether or not this file or folder is in fact a directory
    pub fn directory(&self) -> bool {
        (self.bit_field & 0x10) != 0
    }

    /// Whether or not this file or folder is temporary and
    /// may be cleaned up
    ///
    /// Does not represent children if it is a directory
    pub fn temporary(&self) -> bool {
        (self.bit_field & 0x100) != 0
    }
}

/// Represents the file information for a file
///
/// Cannot be determined at compile time, as this language and VM is designed
/// to run accross multiple computers
pub enum VmFileStats {
    WindowsStats(VmWindowsFileStats),
    LinuxStats(VmLinuxFileStats),
}

/// Holds information regarding a directory entry
#[async_trait]
pub trait VmDirEnt {
    fn get_path(&self) -> &Path;

    fn get_name(&self) -> &OsStr;

    fn is_file(&self) -> bool;

    fn file_stats(&self) -> Result<VmFileStats, RuntimeError>;

    fn open_file(&self, open_options: Option<OpenOptions>)
        -> Result<Arc<dyn VmFile>, RuntimeError>;
}

/// Holds the result from a directory entry request
pub trait VmDirEntResult {
    fn get_dir_ents(&self) -> Arc<dyn Iterator<Item = &'_ dyn VmDirEnt>>;
}

/// Represents a file system that can be used to open or close files, or
/// browse for directory entries
#[async_trait]
pub trait VmFs {
    async fn list_dir(
        &self,
        position: &Position,
        path: &Path,
    ) -> Result<Arc<dyn VmDirEntResult>, RuntimeError>;

    async fn open_file(
        &self,
        position: &Position,
        path: &Path,
        open_options: Option<OpenOptions>,
    ) -> Result<Arc<dyn VmFile>, RuntimeError>;
}

pub enum ModuleLoadResult<T: VmContext> {
    Environment(Environment<T>),
    FileContents(String),
}

/// Supports the (include) function inside the environment, to allow for determining
/// where and how to load source code for modules
pub trait VmModuleHandler<T: VmContext> {
    fn load_module_contents(
        &self,
        current_module_path: Option<&Path>,
        module_path: Arc<str>,
    ) -> Result<ModuleLoadResult<T>, RuntimeError>;

    fn is_standard_library_module(&self, module_path: &str) -> bool {
        module_path.starts_with("std:")
    }

    fn load_standard_library_module(
        &self,
        module_path: Arc<str>,
    ) -> Result<ModuleLoadResult<T>, RuntimeError> {
        stdlib::load_standard_lib_module(&module_path).map(ModuleLoadResult::Environment)
    }
}

/// Represents something that the VM can write to or read from
///
/// Seeking isn't as important as reading and writing, and dropping
/// seek allows for structures such as pipes
pub trait VmFile: tokio::io::AsyncRead + tokio::io::AsyncWrite {
    fn get_path(&self) -> Option<&Path>;
}

/// The trait that must be implemented for types that are going to be used in the
/// Lisp environment as a context
pub trait VmContext {
    fn get_console(&self) -> Arc<dyn VmFile>;

    fn get_fs<ID: Hash>(&self, system_id: Option<ID>) -> Arc<dyn VmFs>;

    fn get_module_handler(&self) -> Arc<dyn VmModuleHandler<Self>>;
}

pub mod defaults {
    use std::{fs::OpenOptions, path::PathBuf};

    use async_trait::async_trait;
    use pin_project::pin_project;
    use tokio::io::{AsyncRead, AsyncWrite};

    use crate::vm::error::{man_convert_to_err, RuntimeErrorKind};

    use super::*;

    #[pin_project]
    pub struct Console {
        #[pin]
        stdin: tokio::io::Stdin,
        #[pin]
        stdout: tokio::io::Stdout,
    }

    impl AsyncRead for Console {
        fn poll_read(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            buf: &mut tokio::io::ReadBuf<'_>,
        ) -> std::task::Poll<std::io::Result<()>> {
            let this = self.project();
            this.stdin.poll_read(cx, buf)
        }
    }

    impl AsyncWrite for Console {
        fn poll_write(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            buf: &[u8],
        ) -> std::task::Poll<Result<usize, std::io::Error>> {
            let this = self.project();
            this.stdout.poll_write(cx, buf)
        }

        fn poll_flush(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<Result<(), std::io::Error>> {
            let this = self.project();
            this.stdout.poll_flush(cx)
        }

        fn is_write_vectored(&self) -> bool {
            self.stdout.is_write_vectored()
        }

        fn poll_shutdown(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<Result<(), std::io::Error>> {
            let this = self.project();
            this.stdout.poll_shutdown(cx)
        }

        fn poll_write_vectored(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            bufs: &[std::io::IoSlice<'_>],
        ) -> std::task::Poll<Result<usize, std::io::Error>> {
            let this = self.project();
            this.stdout.poll_write_vectored(cx, bufs)
        }
    }

    impl VmFile for Console {
        fn get_path(&self) -> Option<&Path> {
            None
        }
    }

    impl Console {
        pub fn new() -> Self {
            Self {
                stdin: tokio::io::stdin(),
                stdout: tokio::io::stdout(),
            }
        }
    }

    impl Default for Console {
        fn default() -> Self {
            Self::new()
        }
    }

    #[pin_project]
    pub struct File {
        #[pin]
        file: tokio::fs::File,
        path: PathBuf,
    }

    impl AsyncRead for File {
        fn poll_read(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            buf: &mut tokio::io::ReadBuf<'_>,
        ) -> std::task::Poll<std::io::Result<()>> {
            let this = self.project();
            this.file.poll_read(cx, buf)
        }
    }

    impl AsyncWrite for File {
        fn poll_write(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            buf: &[u8],
        ) -> std::task::Poll<Result<usize, std::io::Error>> {
            let this = self.project();
            this.file.poll_write(cx, buf)
        }

        fn poll_flush(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<Result<(), std::io::Error>> {
            let this = self.project();
            this.file.poll_flush(cx)
        }

        fn is_write_vectored(&self) -> bool {
            self.file.is_write_vectored()
        }

        fn poll_shutdown(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<Result<(), std::io::Error>> {
            let this = self.project();
            this.file.poll_shutdown(cx)
        }

        fn poll_write_vectored(
            self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            bufs: &[std::io::IoSlice<'_>],
        ) -> std::task::Poll<Result<usize, std::io::Error>> {
            let this = self.project();
            this.file.poll_write_vectored(cx, bufs)
        }
    }

    impl VmFile for File {
        fn get_path(&self) -> Option<&Path> {
            Some(&self.path)
        }
    }

    pub struct Fs;

    #[async_trait]
    impl VmFs for Fs {
        async fn list_dir(
            &self,
            _position: &Position,
            _path: &Path,
        ) -> Result<Arc<dyn VmDirEntResult>, RuntimeError> {
            todo!()
        }

        async fn open_file(
            &self,
            position: &Position,
            path: &Path,
            open_options: Option<OpenOptions>,
        ) -> Result<Arc<dyn VmFile>, RuntimeError> {
            let file = open_options
                .map(tokio::fs::OpenOptions::from)
                .unwrap_or_else(|| {
                    let mut options = tokio::fs::OpenOptions::new();
                    options.read(true);
                    options
                })
                .open(path)
                .await
                .map_err(man_convert_to_err(
                    &"<ctx internal>",
                    position,
                    &RuntimeErrorKind::Io,
                ))?;

            Ok(Arc::new(File {
                file,
                path: path.to_owned(),
            }))
        }
    }

    pub struct ModuleHandler;

    impl<T: VmContext> VmModuleHandler<T> for ModuleHandler {
        fn load_module_contents(
            &self,
            current_module_path: Option<&Path>,
            module_path: Arc<str>,
        ) -> Result<ModuleLoadResult<T>, RuntimeError> {
            if <ModuleHandler as VmModuleHandler<T>>::is_standard_library_module(self, &module_path)
            {
                return self.load_standard_library_module(module_path);
            }

            todo!()
        }
    }
}

impl VmContext for () {
    fn get_console(&self) -> Arc<dyn VmFile> {
        Arc::from(defaults::Console::new())
    }

    fn get_fs<ID: Hash>(&self, _system_id: Option<ID>) -> Arc<dyn VmFs> {
        todo!()
    }

    fn get_module_handler(&self) -> Arc<dyn VmModuleHandler<Self>> {
        todo!()
    }
}

#[repr(transparent)]
pub struct SimpleContext<T> {
    inner_data: T,
}

impl<T> SimpleContext<T> {
    pub fn new(inner_data: T) -> Self {
        Self { inner_data }
    }
}

impl<T> std::ops::Deref for SimpleContext<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner_data
    }
}

impl<T> std::ops::DerefMut for SimpleContext<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner_data
    }
}

impl<T> VmContext for SimpleContext<T> {
    fn get_console(&self) -> Arc<dyn VmFile> {
        ().get_console()
    }

    fn get_fs<ID: Hash>(&self, system_id: Option<ID>) -> Arc<dyn VmFs> {
        ().get_fs(system_id)
    }

    fn get_module_handler(&self) -> Arc<dyn VmModuleHandler<Self>> {
        todo!()
    }
}
