#![no_std]
#![feature(alloc_error_handler)]

use core::alloc::{GlobalAlloc, Layout};

const MIN_ALLOC_LIMIT: u32 = 16;

pub struct Alloc {
    pub origin: u64,
    pub end: u64,
}
impl Alloc {
    pub const fn static_allocator() -> Self {
        Alloc {
            origin: 0x0000_1000,
            end: 0x0080_0000,
        }
    }
    pub fn init_allocator(&mut self) {
        let h = self.header_from_start();
        unsafe { h.set_block_size(self.heap_size()) };
        h.status = 0b111;
    }
    fn header_from_start(&self) -> &mut Header {
        unsafe { &mut *(self.origin as *mut Header) }
    }
    fn heap_size(&self) -> u32 {
        let s = self.end - self.origin;
        let limit = 0xFFFF_FFFF;
        if s > limit {
            panic!("Heap too big")
        }
        s as u32
    }
    pub unsafe fn update_alloc_end(&mut self, end: *const u8) {
        let h = self.header_from_start();
        if !h.is_tail() {
            panic!("Try update not tail")
        }
        let size = end as u64 - self.origin;
        h.set_block_size(size as u32);
        self.end = end as u64;
    }
    pub unsafe fn free_custom_block(ptr: *mut u8) {
        Header::from_data(ptr).dealloc().unwrap()
    }
    pub unsafe fn mark_custom_block(&mut self, block: &[u8]) {
        let new_h = block.as_ptr() as u64 - 16;

        let mut h = self.header_from_start();
        loop {
            if let Some(next_h) = h.next_header() {
                if (h as *mut Header as u64) < new_h && new_h < (next_h as *mut Header as u64) {
                    break;
                } else {
                    h = next_h;
                }
            } else {
                break;
            }
        }

        let size_to_block = new_h - h as *mut Header as u64;
        let block_size = compute_size(block.len());

        if !h.is_free() {
            panic!("Not free")
        }

        h.alloc(size_to_block as u32).unwrap();
        h.set_free(true).unwrap();
        let next_h = h.next_header().unwrap();
        if next_h as *mut Header as u64 != new_h {
            panic!("Next headers do not match")
        }
        next_h.alloc(block_size).unwrap();
    }
    unsafe fn alloc(&self, size: u32) -> Result<*mut u8, AllocError> {
        let mut p = self.header_from_start();

        loop {
            if p.is_free() && p.block_size() >= size {
                p.alloc(size)?;
                return Ok(p.data());
            }

            if let Some(next_p) = p.next_header() {
                p = next_p;
            } else {
                return Err(alloc_error!(OutOfMemory));
            }
        }
    }
    pub fn alloc_size(&mut self, size: u32) -> *mut u8 {
        unsafe { GlobalAlloc::alloc(self, Layout::from_size_align_unchecked(size as usize, 0)) }
    }
    pub fn dealloc_ptr(&mut self, ptr: *mut u8) {
        unsafe { GlobalAlloc::dealloc(self, ptr, Layout::from_size_align_unchecked(0, 0)) }
    }
}

#[derive(Debug)]
enum AllocErrorType {
    TryAllocNonFreeBlock,
    NextHeaderSmallThanSelf,
    PrevHeaderBiggerThanSelf,
    NoNextHeader,
    NoPrevHeader,
    LostLink,
    OutOfMemory,
    AlreadyFree,
    InconsistantSize,
    TryAllocTail,
}

#[derive(Debug)]
struct AllocError {
    error_type: AllocErrorType,
    line: u32,
}

#[macro_export]
macro_rules! alloc_error {
    ($t:ident) => {
        AllocError {
            error_type: AllocErrorType::$t,
            line: line!(),
        }
    };
}

fn compute_size(bytes: usize) -> u32 {
    let align_16 = 1 + (bytes >> 4) + if (bytes & 0xF) != 0 { 1 } else { 0 };
    (align_16 as u32) << 4
}

struct HeaderBuilder {
    at: *mut Header,
    block_size: u32,
}
impl HeaderBuilder {
    unsafe fn build<'a>(self) -> &'a mut Header {
        let h = &mut *self.at;

        h.set_block_size(self.block_size);
        h.status = Header::FREE_BIT;

        h
    }
}

#[repr(packed)]
struct Header {
    next_header: u64,
    prev_size: u32,
    status: u32,
    //
    data: u32,
}
impl Header {
    const FREE_BIT: u32 = 1 << 0;
    const TAIL_BIT: u32 = 1 << 1;
    const HEAD_BIT: u32 = 1 << 2;

    #[inline]
    unsafe fn from_data<'a>(p: *mut u8) -> &'a mut Self {
        &mut *((p as *mut u32).offset(-4) as *mut Header)
    }
    #[inline]
    unsafe fn data(&self) -> *mut u8 {
        (&self.data) as *const u32 as *mut u8
    }
    #[inline]
    unsafe fn is_free(&self) -> bool {
        (self.status & Self::FREE_BIT) != 0
    }
    unsafe fn set_free(&mut self, val: bool) -> Result<(), AllocError> {
        if !val && self.is_tail() {
            return Err(alloc_error!(TryAllocTail));
        }

        self.status &= !(Self::FREE_BIT);
        if val {
            self.status |= Self::FREE_BIT;
        }
        Ok(())
    }
    #[inline]
    unsafe fn is_tail(&self) -> bool {
        (self.status & Self::TAIL_BIT) != 0
    }
    unsafe fn set_tail(&mut self, val: bool) -> Result<(), AllocError> {
        if val && (!self.is_free()) {
            return Err(alloc_error!(TryAllocTail));
        }

        self.status &= !(Self::TAIL_BIT);
        if val {
            self.status |= Self::TAIL_BIT;
        }

        Ok(())
    }
    #[inline]
    unsafe fn is_head(&self) -> bool {
        (self.status & Self::HEAD_BIT) != 0
    }
    #[inline]
    unsafe fn block_size(&self) -> u32 {
        (self.next_header - self as *const Header as u64) as u32
    }
    #[inline]
    unsafe fn offset(&self, off: isize) -> *mut Header {
        (self as *const Header as *mut u8).offset(off) as *mut Header
    }
    unsafe fn next_header<'a>(&self) -> Option<&'a mut Self> {
        if self.is_tail() {
            None
        } else {
            Some(&mut *(self.next_header as *mut Header))
        }
    }
    unsafe fn prev_header<'a>(&self) -> Option<&'a mut Self> {
        if self.is_head() {
            None
        } else {
            let p = self as *const Header as *mut Header as *mut u8;
            let p_prev = p.offset(-(self.prev_size as isize)) as *mut Header;
            Some(&mut *p_prev)
        }
    }
    unsafe fn set_block_size(&mut self, new_size: u32) {
        self.next_header = ((self as *const Header) as u64) + new_size as u64;
    }
    unsafe fn update_next(&mut self, next: &mut Header) -> Result<(), AllocError> {
        if &*self < next {
            self.next_header = next as *const Header as u64;
            next.prev_size = self.block_size();

            if self.is_tail() {
                self.set_tail(false)?;
                next.set_tail(true)?;
            }

            test_link(self, next)
        } else {
            Err(alloc_error!(NextHeaderSmallThanSelf))
        }
    }
    unsafe fn update_prev(&mut self, prev: &mut Header) -> Result<(), AllocError> {
        if &*self > prev {
            prev.next_header = self as *const Header as u64;
            self.prev_size = prev.block_size();

            test_link(prev, self)
        } else {
            Err(alloc_error!(PrevHeaderBiggerThanSelf))
        }
    }
    unsafe fn insert(&mut self, at: &mut Header) -> Result<(), AllocError> {
        if let Some(next_header) = self.next_header() {
            next_header.update_prev(at)?;
        }
        self.update_next(at)?;

        Ok(())
    }
    unsafe fn alloc(&mut self, size: u32) -> Result<(), AllocError> {
        if !self.is_free() {
            return Err(alloc_error!(TryAllocNonFreeBlock));
        }

        let remaning_size = self.block_size() - size;
        if remaning_size >= MIN_ALLOC_LIMIT {
            self.insert(
                HeaderBuilder {
                    at: self.offset(size as isize),
                    block_size: self.block_size() - size,
                }
                .build(),
            )?;
        }

        self.set_free(false)?;

        Ok(())
    }
    unsafe fn dealloc(&mut self) -> Result<(), AllocError> {
        if self.is_free() {
            Err(alloc_error!(AlreadyFree))
        } else {
            let next_header = self.next_header().ok_or(alloc_error!(NoNextHeader))?;

            match self.prev_header() {
                Some(prev_header) if prev_header.is_free() => {
                    prev_header.update_next(next_header)?;
                    next_header.update_prev(prev_header)?;
                    prev_header.set_free(false)?;
                    prev_header.dealloc()?;
                }
                _ => {
                    if next_header.is_free() {
                        if let Some(next_next_header) = next_header.next_header() {
                            self.update_next(next_next_header)?;
                            next_next_header.update_prev(self)?;
                        } else {
                            let total_size = self.block_size() + next_header.block_size();
                            self.set_block_size(total_size);
                            self.set_free(true)?;
                            self.set_tail(true)?;
                        }
                    }
                    self.set_free(true)?;
                }
            }
            Ok(())
        }
    }
    unsafe fn shrink_to(&mut self, new_size: u32) -> Result<(), AllocError> {
        self.insert(
            HeaderBuilder {
                at: self.offset(new_size as isize),
                block_size: self.block_size() - new_size,
            }
            .build(),
        )?;

        Ok(())
    }
    unsafe fn try_grow_to(&mut self, new_size: u32) -> Result<bool, AllocError> {
        let next_header = self.next_header().ok_or(alloc_error!(NoNextHeader))?;
        if !next_header.is_free() {
            return Ok(false);
        }

        let size = self.block_size() + next_header.block_size();

        if size < new_size {
            return Ok(false);
        }

        if let Some(next_next_header) = next_header.next_header() {
            self.update_next(next_next_header)?;
            next_next_header.update_prev(self)?;
        } else {
            self.set_block_size(size);
            self.set_free(true)?;
            self.set_tail(true)?;
        }

        if size - self.block_size() > MIN_ALLOC_LIMIT || self.is_tail() {
            self.insert(
                HeaderBuilder {
                    at: self.offset(new_size as isize),
                    block_size: self.block_size() - new_size,
                }
                .build(),
            )?;
        }

        self.set_free(false)?;

        Ok(true)
    }
}
impl core::cmp::PartialEq for Header {
    #[inline]
    fn eq(&self, other: &Header) -> bool {
        self as *const Header as u64 == other as *const Header as u64
    }
}
impl core::cmp::PartialOrd for Header {
    fn partial_cmp(&self, other: &Header) -> Option<core::cmp::Ordering> {
        let x = self as *const Header as u64;
        let y = other as *const Header as u64;
        if x < y {
            Some(core::cmp::Ordering::Less)
        } else if x > y {
            Some(core::cmp::Ordering::Greater)
        } else {
            Some(core::cmp::Ordering::Equal)
        }
    }
}

unsafe fn test_link(prev: &Header, next: &Header) -> Result<(), AllocError> {
    let n1 = prev as *const Header as u64 + prev.block_size() as u64;
    let n2 = next as *const Header as u64;
    if n1 != n2 {
        return Err(alloc_error!(InconsistantSize));
    }

    let pnh = prev.next_header().ok_or(alloc_error!(NoNextHeader))?;
    let nph = next.prev_header().ok_or(alloc_error!(NoPrevHeader))?;

    if pnh != next || nph != prev {
        return Err(alloc_error!(LostLink));
    }

    Ok(())
}

unsafe impl GlobalAlloc for Alloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let size = compute_size(layout.size());

        match self.alloc(size) {
            Ok(x) => x,
            Err(_e) => 0 as *mut u8,
        }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        match Header::from_data(ptr).dealloc() {
            Ok(()) => {}
            Err(_e) => {}
        }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let old_size = compute_size(layout.size());
        let new_size = compute_size(new_size);

        let h = Header::from_data(ptr);

        if new_size == old_size {
            ptr
        } else if new_size < old_size {
            match h.shrink_to(new_size) {
                Ok(()) => ptr,
                Err(_e) => 0 as *mut u8,
            }
        } else {
            match h.try_grow_to(new_size) {
                Ok(x) if x => ptr,
                Ok(_) => {
                    let new_ptr = GlobalAlloc::alloc(
                        self,
                        Layout::from_size_align_unchecked(new_size as usize, layout.align()),
                    );
                    core::ptr::copy_nonoverlapping(ptr, new_ptr, new_size as usize);
                    self.dealloc(ptr, layout);

                    new_ptr
                }
                Err(_e) => 0 as *mut u8,
            }
        }
    }
}
