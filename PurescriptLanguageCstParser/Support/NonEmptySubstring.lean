module

public import NonEmpty.String
import Init.Data.String.Substring
import Init.Data.String.Lemmas.IsEmpty

public section
namespace NonEmpty.String

/--
A non-empty string slice.

Despite the historical name, this intentionally wraps `String.Slice`, not `Substring.Raw`, because
`String.Slice` is the safe API Lean is moving toward.
-/
structure NonEmptySubstring where
  toSlice : String.Slice
  isNonEmpty : toSlice.isEmpty = false

instance : CoeOut NonEmptySubstring String.Slice where
  coe s := s.toSlice

instance : ToString NonEmptySubstring where
  toString s := s.toSlice.copy

instance : BEq NonEmptySubstring where
  beq a b := a.toSlice == b.toSlice

instance : Hashable NonEmptySubstring where
  hash s := hash s.toSlice

instance : LT NonEmptySubstring where
  lt a b := a.toSlice < b.toSlice

instance : Ord NonEmptySubstring where
  compare a b := compare a.toSlice b.toSlice

namespace NonEmptySubstring

@[inline] def fromSlice? (s : String.Slice) : Option NonEmptySubstring :=
  if h : s.isEmpty = false then some ⟨s, h⟩ else none

@[inline] def fromString? (s : String) : Option NonEmptySubstring :=
  fromSlice? s.toSlice

@[inline] def fromRawSubstring? (s : Substring.Raw) : Option NonEmptySubstring :=
  s.toSlice?.bind fromSlice?

@[inline] def toString (s : NonEmptySubstring) : String :=
  s.toSlice.copy

@[inline] def toRawSubstring (s : NonEmptySubstring) : Substring.Raw :=
  Substring.Raw.ofSlice s.toSlice

@[inline] def toNonEmptyString (s : NonEmptySubstring) : NonEmptyString :=
  ⟨s.toString, by
    simpa [toString] using (String.Slice.copy_ne_empty_iff).2 s.isNonEmpty⟩

@[simp] theorem toString_ne_empty (s : NonEmptySubstring) : s.toString ≠ "" := by
  simpa [toString] using (String.Slice.copy_ne_empty_iff).2 s.isNonEmpty

@[inline] def front (s : NonEmptySubstring) : Char :=
  s.toSlice.front

@[inline] def back (s : NonEmptySubstring) : Char :=
  s.toSlice.back

end NonEmptySubstring

end NonEmpty.String
