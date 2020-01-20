use std::{
    ops::{Deref, DerefMut, Range, Index, IndexMut},
    iter::FromIterator,
    any,
    fmt,
};

#[repr(i8)]
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Trit {
    MinusOne = -1,
    Zero = 0,
    PlusOne = 1,
}

impl From<i8> for Trit {
    fn from(x: i8) -> Self {
        match x {
            -1 => Trit::MinusOne,
            0 => Trit::Zero,
            1 => Trit::PlusOne,
            x => panic!("Invalid trit representation '{}'", x),
        }
    }
}

impl Trit {
    fn from_u8(x: u8) -> Self {
        match x {
            0 => Trit::MinusOne,
            1 => Trit::Zero,
            2 => Trit::PlusOne,
            x => panic!("Invalid trit representation '{}'", x),
        }
    }

    fn into_u8(self) -> u8 {
        match self {
            Trit::MinusOne => 0,
            Trit::Zero => 1,
            Trit::PlusOne => 2,
        }
    }
}

impl fmt::Debug for Trit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Trit::MinusOne => write!(f, "{}", -1),
            Trit::Zero => write!(f, "{}", 0),
            Trit::PlusOne => write!(f, "{}", 1),
        }
    }
}

impl Into<i8> for Trit {
    fn into(self) -> i8 {
        match self {
            Trit::MinusOne => -1,
            Trit::Zero => 0,
            Trit::PlusOne => 1,
        }
    }
}

pub trait RawTritSlice {
    /// Get the number of trits in this buffer
    fn len(&self) -> usize;

    /// Get the trit at the given index
    unsafe fn get_unchecked(&self, index: usize) -> Trit;

    /// Set the trit at the given index
    unsafe fn set_unchecked(&mut self, index: usize, trit: Trit);

    /// Get a slice of this slice
    unsafe fn slice_unchecked(&self, range: Range<usize>) -> &Self;

    /// Get a mutable slice of this slice
    unsafe fn slice_unchecked_mut(&mut self, range: Range<usize>) -> &mut Self;
}

pub trait RawTritBuf {
    type Slice: RawTritSlice + ?Sized;

    /// Create a new empty buffer
    fn new() -> Self where Self: Sized;

    /// Create a new buffer containing the given trits
    fn from_trits<T: Into<Trit> + Clone>(trits: &[T]) -> Self where Self: Sized {
        let mut this = Self::new();
        for trit in trits {
            this.push(trit.clone().into());
        }
        this
    }

    /// Push a trit to the back of this buffer
    fn push(&mut self, trit: Trit);

    /// View the trits in this buffer as a slice
    fn as_slice(&self) -> &Self::Slice;

    /// View the trits in this buffer as a mutable slice
    fn as_slice_mut(&mut self) -> &mut Self::Slice;

    /// Convert this encoding into another encoding
    fn into_encoding<T: RawTritBuf>(this: TritBuf<Self>) -> TritBuf<T> where Self: Sized {
        // if TypeId::of::<Self>() == TypeId::of::<T>() {
        //     unsafe { std::mem::transmute(this) }
        // } else {
            this.iter().collect()
        // }
    }
}

// T1B1

pub struct T1B1Slice([()]);

impl T1B1Slice {
    unsafe fn make(ptr: *const u8, offset: usize, len: usize) -> *const Self {
        std::mem::transmute((ptr.offset(offset as isize), len))
    }

    unsafe fn ptr(&self, index: usize) -> *const u8 {
        (self.0.as_ptr() as *const u8).offset(index as isize)
    }
}

impl RawTritSlice for T1B1Slice {
    fn len(&self) -> usize {
        self.0.len()
    }

    unsafe fn get_unchecked(&self, index: usize) -> Trit {
        Trit::from_u8(self.ptr(index).read())
    }

    unsafe fn set_unchecked(&mut self, index: usize, trit: Trit) {
        (self.ptr(index) as *mut u8).write(trit.into_u8());
    }

    unsafe fn slice_unchecked(&self, range: Range<usize>) -> &Self {
        &*Self::make(self.ptr(0), range.start, range.end - range.start)
    }

    unsafe fn slice_unchecked_mut(&mut self, range: Range<usize>) -> &mut Self {
        &mut *(Self::make(self.ptr(0), range.start, range.end - range.start) as *mut _)
    }
}

pub struct T1B1Buf(Vec<u8>);

impl RawTritBuf for T1B1Buf {
    type Slice = T1B1Slice;

    fn new() -> Self {
        Self(Vec::new())
    }

    fn push(&mut self, trit: Trit) {
        self.0.push(trit.into_u8());
    }

    fn as_slice(&self) -> &Self::Slice {
        unsafe { &*Self::Slice::make(self.0.as_ptr() as _, 0, self.0.len()) }
    }

    fn as_slice_mut(&mut self) -> &mut Self::Slice {
        unsafe { &mut *(Self::Slice::make(self.0.as_ptr() as _, 0, self.0.len()) as *mut _) }
    }
}

// B1T3

pub struct T4B1Slice([()]);

impl T4B1Slice {
    unsafe fn make(ptr: *const u8, offset: usize, len: usize) -> *const Self {
        let len = (len << 2) | (offset % 4);
        std::mem::transmute((ptr.offset((offset / 4) as isize), len))
    }

    unsafe fn ptr(&self, index: usize) -> *const u8 {
        let byte_offset = index / 4;
        (self.0.as_ptr() as *const u8).offset(byte_offset as isize)
    }

    fn len_offset(&self) -> (usize, usize) {
        (self.0.len() >> 2, self.0.len() & 0b11)
    }
}

impl RawTritSlice for T4B1Slice {
    fn len(&self) -> usize {
        self.len_offset().0
    }

    unsafe fn get_unchecked(&self, index: usize) -> Trit {
        let b = self.ptr(index).read();
        let trit = (b >> (((self.len_offset().1 + index) % 4) * 2)) & 0b11;
        Trit::from_u8(trit)
    }

    unsafe fn set_unchecked(&mut self, index: usize, trit: Trit) {
        let b = self.ptr(index).read();
        let b = b & !(0b11 << (((self.len_offset().1 + index) % 4) * 2));
        let b = b | (trit.into_u8() << (self.len_offset().1 * 2));
        (self.ptr(index) as *mut u8).write(b);
    }

    unsafe fn slice_unchecked(&self, range: Range<usize>) -> &Self {
        &*Self::make(self.ptr(0), range.start, range.end - range.start)
    }

    unsafe fn slice_unchecked_mut(&mut self, range: Range<usize>) -> &mut Self {
        &mut *(Self::make(self.ptr(0), range.start, range.end - range.start) as *mut Self)
    }
}

pub struct T4B1Buf(Vec<u8>, usize);

impl RawTritBuf for T4B1Buf {
    type Slice = T4B1Slice;

    fn new() -> Self {
        Self(Vec::new(), 0)
    }

    fn push(&mut self, trit: Trit) {
        let b = trit.into_u8();
        if self.1 % 4 == 0 {
            self.0.push(b);
        } else {
            let last_index = self.0.len() - 1;
            unsafe { *self.0.get_unchecked_mut(last_index) |= b << ((self.1 % 4) * 2) };
        }
        self.1 += 1;
    }

    fn as_slice(&self) -> &Self::Slice {
        unsafe { &*Self::Slice::make(self.0.as_ptr() as _, 0, self.1) }
    }

    fn as_slice_mut(&mut self) -> &mut Self::Slice {
        unsafe { &mut *(Self::Slice::make(self.0.as_ptr() as _, 0, self.1) as *mut _) }
    }
}

// API

pub struct TritSlice<T: RawTritSlice + ?Sized = T1B1Slice>(T);

impl<T: RawTritSlice + ?Sized> TritSlice<T> {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn get(&self, index: usize) -> Option<Trit> {
        if index < self.0.len() {
            unsafe { Some(self.0.get_unchecked(index).into()) }
        } else {
            None
        }
    }

    pub fn set(&mut self, index: usize, trit: Trit) {
        if index < self.0.len() {
            unsafe { self.0.set_unchecked(index, trit.into()) };
        }
    }

    pub fn iter(&self) -> impl Iterator<Item=Trit> + '_ {
        (0..self.0.len()).map(move |idx| unsafe { self.0.get_unchecked(idx).into() })
    }

    pub fn slice(&self, range: Range<usize>) -> &Self {
        assert!(range.end >= range.start && range.end <= self.len());
        unsafe { &*(self.0.slice_unchecked(range) as *const _ as *const Self) }
    }

    pub fn slice_mut(&mut self, range: Range<usize>) -> &mut Self {
        assert!(range.end >= range.start && range.end <= self.len());
        unsafe { &mut *(self.0.slice_unchecked_mut(range) as *mut _ as *mut Self) }
    }
}

impl<'a, T: RawTritSlice> fmt::Debug for &'a TritSlice<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TritSlice<{}> [", any::type_name::<T>())?;
        for (i, trit) in self.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", trit)?;
        }
        write!(f, "]")
    }
}

/*
impl<T: RawTritSlice, U: Deref<Target=TritSlice<T>>> Index<Range<usize>> for U {
    type Output = TritSlice<T>;

    fn index(&self, range: Range<usize>) -> &Self::Output {
        self.slice(range)
    }
}
*/

impl<T: RawTritSlice> Index<Range<usize>> for TritSlice<T> {
    type Output = Self;

    fn index(&self, range: Range<usize>) -> &Self::Output {
        self.slice(range)
    }
}

impl<T: RawTritSlice> IndexMut<Range<usize>> for TritSlice<T> {
    fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
        self.slice_mut(range)
    }
}

pub struct TritBuf<T: RawTritBuf = T1B1Buf>(T);

impl<T: RawTritBuf> TritBuf<T> {
    pub fn new() -> Self {
        Self(T::new())
    }

    pub fn from_trits<U: Into<Trit> + Clone>(trits: &[U]) -> Self {
        Self(T::from_trits(trits))
    }

    pub fn push(&mut self, trit: Trit) {
        self.0.push(trit.into());
    }

    pub fn as_slice(&self) -> &TritSlice<T::Slice> {
        unsafe { &*(self.0.as_slice() as *const T::Slice as *const TritSlice<T::Slice>) }
    }

    pub fn as_slice_mut(&mut self) -> &mut TritSlice<T::Slice> {
        unsafe { &mut *(self.0.as_slice_mut() as *mut T::Slice as *mut TritSlice<T::Slice>) }
    }

    pub fn into_encoding<U: RawTritBuf>(self) -> TritBuf<U> {
        T::into_encoding(self)
    }
}

impl<T: RawTritBuf> Deref for TritBuf<T> {
    type Target = TritSlice<T::Slice>;

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T: RawTritBuf> DerefMut for TritBuf<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_slice_mut()
    }
}

impl<T: RawTritBuf> FromIterator<Trit> for TritBuf<T> {
    fn from_iter<I: IntoIterator<Item=Trit>>(iter: I) -> Self {
        let mut this = Self::new();

        for trit in iter {
            this.push(trit);
        }

        this
    }
}

impl<T: RawTritBuf> Index<Range<usize>> for TritBuf<T> {
    type Output = TritSlice<T::Slice>;

    fn index(&self, range: Range<usize>) -> &Self::Output {
        self.slice(range)
    }
}

impl<T: RawTritBuf> IndexMut<Range<usize>> for TritBuf<T> {
    fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
        self.slice_mut(range)
    }
}

impl<T: RawTritBuf> fmt::Debug for TritBuf<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TritBuf<{}> [", any::type_name::<T>())?;
        for (i, trit) in self.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", trit)?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compare() {
        fn slices_eq(a: &TritSlice<T4B1Slice>, b: &TritSlice<T4B1Slice>) -> bool {
            a
                .iter()
                .zip(b.iter())
                .all(|(a, b)| a == b)
        }

        let mut a = TritBuf::<T4B1Buf>::from_trits(&[1i8, -1, 0, 1, 0])
            .into_encoding::<T1B1Buf>()
            .into_encoding::<T4B1Buf>();

        a.set(2, Trit::MinusOne);

        let b = TritBuf::<T4B1Buf>::from_trits(&[-1i8, -1, 1]);

        assert!(slices_eq(&a[1..5], &b));
    }
}
