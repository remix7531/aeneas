import Aeneas.Std.Core.Fmt
import Aeneas.Std.Array.Array
import Aeneas.Std.Slice
import Aeneas.Std.Range
import Aeneas.Data.List.List
import Aeneas.Std.Core.Convert
import Aeneas.Std.Core.Cmp

/-! Array definitions which mention slices -/

namespace Aeneas.Std

open Result Error core.ops.range WP

attribute [-simp] List.getElem!_eq_getElem?_getD

/-! Array to slice/subslices -/

@[step_pure_def]
def Array.to_slice {α : Type u} {n : Usize} (v : Array α n) : Slice α :=
  ⟨ v.val, by scalar_tac ⟩

def Array.from_slice {α : Type u} {n : Usize} (a : Array α n) (s : Slice α) : Array α n :=
  if h: s.val.length = n.val then
    ⟨ s.val, by simp [*] ⟩
  else a -- Unreachable case

@[simp]
theorem Array.from_slice_val {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α) (h : ns.val.length = n.val) :
  (from_slice a ns).val = ns.val
  := by simp [from_slice, *]

@[step_pure_def]
def Array.to_slice_mut {α : Type u} {n : Usize} (a : Array α n) :
  Slice α × (Slice α → Array α n) :=
  (Array.to_slice a, Array.from_slice a)

def Array.subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end.val ∧ r.end.val ≤ a.val.length then
    ok ⟨ a.val.slice r.start.val r.end.val,
          by
            have := a.val.slice_length_le r.start.val r.end.val
            scalar_tac ⟩
  else
    fail panic

@[step]
theorem Array.subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ a.val.length) :
  subslice a r ⦃ s =>
  s.val = a.val.slice r.start.val r.end.val ∧
  (∀ i, i + r.start.val < r.end.val → s.val[i]! = a.val[r.start.val + i]!) ⦄
  := by
  simp only [subslice, true_and, h0, h1, ↓reduceIte, spec_ok, true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end.val i a.val (by scalar_tac)
  simp only [this]


def Array.update_subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) (s : Slice α) : Result (Array α n) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end.val ∧ r.end.val ≤ a.length ∧ s.val.length = r.end.val - r.start.val then
    ok ⟨ a.val.setSlice! r.start s.val, by scalar_tac ⟩
  else
    fail panic

-- TODO: it is annoying to write `.val` everywhere. We could leverage coercions,
-- but: some symbols like `+` are already overloaded to be notations for monadic
-- operations/
-- We should introduce special symbols for the monadic arithmetic operations
-- (the user will never write those symbols directly).
@[step]
theorem Array.update_subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
  (_ : r.start.val < r.end.val) (_ : r.end.val ≤ a.length) (_ : s.length = r.end.val - r.start.val) :
  update_subslice a r s ⦃ na =>
  (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
  (∀ i, r.start.val ≤ i → i < r.end.val → na[i]! = s[i - r.start.val]!) ∧
  (∀ i, r.end.val ≤ i → i < n.val → na[i]! = a[i]!) ⦄ := by
  simp [update_subslice]
  split
  . simp [spec_ok]
    simp_lists
  . scalar_tac

@[rust_fun "core::array::{core::ops::index::Index<[@T; @N], @I, @O>}::index"]
def core.array.Array.index
  {T I Output : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output)
  (a : Array T N) (i : I) : Result Output :=
  inst.index a.to_slice i

@[rust_fun "core::array::{core::ops::index::IndexMut<[@T; @N], @I, @O>}::index_mut"]
def core.array.Array.index_mut
  {T I Output : Type} {N : Usize} (inst : core.ops.index.IndexMut (Slice T) I Output)
  (a : Array T N) (i : I) :
  Result (Output × (Output → Array T N)) := do
  let (s, back) ← inst.index_mut a.to_slice i
  ok (s, fun o => Array.from_slice a (back o))

@[rust_trait_impl "core::ops::index::Index<[@T; @N], @I, @O>"]
def core.ops.index.IndexArray {T I Output : Type} {N : Usize}
  (inst : core.ops.index.Index (Slice T) I Output) :
  core.ops.index.Index (Array T N) I Output := {
  index := core.array.Array.index inst
}

@[rust_trait_impl "core::ops::index::IndexMut<[@T; @N], @I, @O>"]
def core.ops.index.IndexMutArray {T I Output : Type} {N : Usize}
  (inst : core.ops.index.IndexMut (Slice T) I Output) :
  core.ops.index.IndexMut (Array T N) I Output := {
  indexInst := core.ops.index.IndexArray inst.indexInst
  index_mut := core.array.Array.index_mut inst
}

@[reducible, rust_type "core::array::TryFromSliceError"]
def core.array.TryFromSliceError := Unit

@[simp, simp_lists_safe, grind =, agrind =]
theorem Array.val_to_slice {α} {n} (a : Array α n) : a.to_slice.val = a.val := by
  simp only [Array.to_slice]

@[simp, simp_lists_safe, simp_scalar_safe, scalar_tac a.to_slice]
theorem Array.length_to_slice (a : Array α n) :
  a.to_slice.length = n := by
  simp only [Slice.length, Array.to_slice, List.Vector.length_val]

grind_pattern Array.length_to_slice => a.to_slice
grind_pattern [agrind] Array.length_to_slice => a.to_slice

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::eq"]
def core.array.equality.PartialEqArray.eq
  {T : Type} {U : Type} {N : Usize} (partialEqInst : core.cmp.PartialEq T U)
  (a0 : Array T N) (a1 : Array U N) : Result Bool := do
  if a0.length = a1.length then
    List.allM (fun (x, y) => partialEqInst.eq x y) (List.zip a0.val a1.val)
  else .ok false

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::ne"]
def core.array.equality.PartialEqArray.ne
  {T : Type} {U : Type} {N : Usize} (partialEqInst : core.cmp.PartialEq T U)
  (a0 : Array T N) (a1 : Array U N) : Result Bool := do
  if a0.length = a1.length then
    List.anyM (fun (x, y) => partialEqInst.ne x y) (List.zip a0.val a1.val)
  else .ok true

@[rust_fun "core::array::{core::fmt::Debug<core::array::TryFromSliceError>}::fmt"]
def core.array.DebugTryFromSliceError.fmt
  (_ : core.array.TryFromSliceError) (fmt : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: this model is simplistic
  .ok (.Ok (), fmt)

@[reducible, rust_trait_impl
  "core::fmt::Debug<core::array::TryFromSliceError>"]
def core.fmt.DebugTryFromSliceError : core.fmt.Debug
  core.array.TryFromSliceError := {
  fmt := core.array.DebugTryFromSliceError.fmt
}

@[rust_fun "core::array::{core::convert::TryFrom<[@T; @N], &'0 [@T], core::array::TryFromSliceError>}::try_from"]
def core.array.TryFromArrayCopySlice.try_from
  {T : Type} (N : Usize) (copyInst : core.marker.Copy T) (s : Slice T) :
  Result (core.result.Result (Array T N) core.array.TryFromSliceError) := do
  if h0: s.length = N then
    match h1: List.mapM copyInst.cloneInst.clone s.val with
    | ok s =>
      ok (.Ok ⟨s, by have := List.mapM_Result_length h1; scalar_tac ⟩)
    | fail e => fail e
    | div => div
  else ok (.Err ())

@[rust_fun "core::array::{core::convert::TryFrom<&'a [@T; @N], &'a [@T], core::array::TryFromSliceError>}::try_from"]
def core.array.TryFromSharedArraySlice.try_from
  {T : Type} (N : Usize) (s : Slice T) :
  Result (core.result.Result (Array T N) core.array.TryFromSliceError) := do
  if h: s.len = N then .ok (.Ok ⟨s.val, by scalar_tac⟩)
  else .ok (.Err ())

/-- When the slice has the right length, `try_from` returns `.Ok` with the
slice contents repackaged as an array. -/
@[step]
theorem core.array.TryFromSharedArraySlice.try_from.step_spec
    {T : Type} (N : Usize) (s : Slice T) (h : s.length = N.val) :
    core.array.TryFromSharedArraySlice.try_from N s
      ⦃ r => ∃ a : Array T N, r = core.result.Result.Ok a ∧ a.val = s.val ⦄ := by
  unfold core.array.TryFromSharedArraySlice.try_from
  have hlen : s.len = N := UScalar.eq_of_val_eq (by simp [h])
  simp [hlen]

/-- `Result.unwrap` extracts the value when the result is statically known
to be `.Ok`. -/
@[step]
theorem core.result.Result.unwrap.step_spec
    {T E : Type} (D : core.fmt.Debug E) (r : core.result.Result T E) (a : T)
    (h : r = core.result.Result.Ok a) :
    core.result.Result.unwrap D r ⦃ x => x = a ⦄ := by
  rw [h]; simp [core.result.Result.unwrap]

@[reducible, rust_trait_impl
  "core::convert::TryFrom<&'a [@T; @N], &'a [@T], core::array::TryFromSliceError>"]
def core.convert.TryFromSharedArraySliceTryFromSliceError (T : Type) (N : Usize) :
  core.convert.TryFrom (Array T N) (Slice T)
  core.array.TryFromSliceError := {
  try_from := core.array.TryFromSharedArraySlice.try_from N
}

/-- When `clone` on the underlying type is the identity (i.e. `clone x = ok x`,
which is the case for every scalar `Copy` instance Aeneas generates), the
copy variant of `try_from` returns `.Ok` with the slice contents preserved.

Phrased generically so callers can specialise to whatever `Copy` instance
they are working with by providing the trivial `clone`-is-identity fact. -/
@[step]
theorem core.array.TryFromArrayCopySlice.try_from.step_spec
    {T : Type} (N : Usize) (copyInst : core.marker.Copy T) (s : Slice T)
    (h : s.length = N.val)
    (hclone : ∀ x : T, copyInst.cloneInst.clone x = Result.ok x) :
    core.array.TryFromArrayCopySlice.try_from N copyInst s
      ⦃ r => ∃ a : Array T N, r = core.result.Result.Ok a ∧ a.val = s.val ⦄ := by
  unfold core.array.TryFromArrayCopySlice.try_from
  simp only [h, ↓reduceDIte]
  have hmap : List.mapM (m := Result) copyInst.cloneInst.clone s.val =
              Result.ok s.val := by
    induction s.val with
    | nil => rfl
    | cons x xs ih => rw [List.mapM_cons, hclone, ih]; rfl
  split
  · case _ s' h1 => cases h1.symm.trans hmap; simp
  · exfalso; rename_i h1; rw [hmap] at h1; cases h1
  · exfalso; rename_i h1; rw [hmap] at h1; cases h1

@[rust_fun "core::array::{core::convert::TryFrom<&'a mut [@T; @N], &'a mut [@T], core::array::TryFromSliceError>}::try_from"]
def core.array.TryFromMutArraySlice.try_from
  {T : Type} (N : Usize) (s : Slice T) :
  Result (
    core.result.Result (Array T N) core.array.TryFromSliceError ×
    (core.result.Result (Array T N) core.array.TryFromSliceError → Slice T)) :=
  if h: s.len = N then
    let back (a : core.result.Result (Array T N) core.array.TryFromSliceError) : Slice T :=
      match a with
      | .Ok a =>
        if a.length = s.length then ⟨ a.val, by scalar_tac ⟩
        else s
      | _ => s
    ok ((.Ok ⟨ s.val, by scalar_tac⟩, back))
  else ok ((.Err (), fun _ => s))

@[simp, rust_fun "core::array::{core::fmt::Debug<[@T; @N]>}::fmt"]
def core.array.DebugArray.fmt
  {T : Type} {N : Usize} (_ : core.fmt.Debug T) (_ : Array T N) (fmt : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: this model is simplistic
  ok (.Ok (), fmt)

@[rust_fun "core::array::{[@T; @N]}::as_slice"]
def core.array.Array.as_slice {T : Type} {N : Usize} (a : Array T N) : Result (Slice T) :=
  ok (⟨ a.val, by scalar_tac ⟩)

@[rust_fun "core::array::{[@T; @N]}::as_mut_slice"]
def core.array.Array.as_mut_slice
  {T : Type} {N : Usize} (a : Array T N) :
  Result (Slice T × (Slice T → Array T N)) :=
  let back (s : Slice T) : Array T N :=
    if h: s.length = N then ⟨ s.val, by scalar_tac ⟩
    else a
  ok (⟨ a.val, by scalar_tac ⟩, back)

@[simp, step_simps]
theorem Array.index_SliceIndexRangeUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.Range Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeUsizeSlice.index r a.to_slice := by rfl

@[step]
theorem Array.index_mut_SliceIndexRangeUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.Range Usize)
    (h0 : r.start ≤ r.end) (h1 : r.end ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r
    ⦃ (s, back) =>
      s.val = a.val.slice r.start r.end ∧
      s.length = r.end.val - r.start.val ∧
      ∀ s', (back s').val = a.val.setSlice! r.start.val s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    show r.start ≤ r.end ∧ (r.end : Usize) ≤ a.to_slice.length from ⟨h0, by scalar_tac⟩]
  refine ⟨?_, ?_, ?_⟩
  · simp [Array.to_slice]
  · simp [Slice.length, List.slice_length]; scalar_tac
  · intro s'; simp [Array.from_slice, Array.to_slice]

-- Array index/index_mut with RangeTo

@[simp, step_simps]
theorem Array.index_SliceIndexRangeToUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeTo Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeToUsizeSlice.index r a.to_slice := by rfl

@[step]
theorem Array.index_mut_SliceIndexRangeToUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeTo Usize)
    (h : r.end ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice T)) a r
    ⦃ (s, back) =>
      s.val = a.val.slice 0 r.end ∧
      s.length = r.end.val ∧
      ∀ s', (back s').val = a.val.setSlice! 0 s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    show (r.end : Usize) ≤ a.to_slice.length from by scalar_tac]
  refine ⟨?_, ?_, ?_⟩
  · simp [Array.to_slice]
  · simp [Slice.length]; scalar_tac
  · intro s'; simp [Array.from_slice, Array.to_slice]

-- Array index/index_mut with RangeFrom

@[simp, step_simps]
theorem Array.index_SliceIndexRangeFromUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeFrom Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeFromUsizeSlice.index r a.to_slice := by rfl

@[step]
theorem Array.index_mut_SliceIndexRangeFromUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeFrom Usize)
    (h : r.start ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice T)) a r
    ⦃ (s, back) =>
      s.val = a.val.drop r.start ∧
      s.length = N.val - r.start.val ∧
      ∀ s', (back s').val = a.val.setSlice! r.start.val s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    Slice.drop,
    show (r.start : Usize) ≤ a.to_slice.length from by scalar_tac]
  refine ⟨?_, ?_, ?_⟩
  · simp [Array.to_slice]
  · simp [Slice.length, List.length_drop]
  · intro s'; simp [Array.from_slice, Array.to_slice]

/-! ## `core::array::from_fn`

Rust's `core::array::from_fn<T, const N: usize>(f: F) -> [T; N]` builds an
array by calling a closure `f` with indices `0, 1, …, N-1`. Aeneas does
not translate this function (higher-order stdlib with internal unsafe
code) and emits an opaque axiom; we provide a concrete model and specs. -/

/-- Recursive worker for `core.array.from_fn`: calls `call` at indices
`i, i+1, …, N-1`, appending each output to `acc`. Terminates on `N - i`. -/
def core.array.from_fn_aux
    {T F : Type} (N : Usize)
    (call : F → Usize → Result (T × F))
    (f : F) (i : Nat) (acc : List T)
    (hacc : acc.length = i) (hi : i ≤ N.val) :
    Result (Array T N) :=
  if h : i < N.val then
    do let idx := Usize.ofNatCore i (by scalar_tac)
       let (val, f') ← call f idx
       core.array.from_fn_aux N call f' (i + 1) (acc ++ [val])
         (by simp [hacc]) (by scalar_tac)
  else
    ok ⟨acc, by scalar_tac⟩
termination_by N.val - i

/-- [core::array::from_fn] -/
@[rust_fun "core::array::from_fn"]
def core.array.from_fn
    {T F : Type} (N : Usize)
    (FnMutInst : core.ops.function.FnMut F Usize T) :
    F → Result (Array T N) :=
  fun f => core.array.from_fn_aux N FnMutInst.call_mut f 0 [] (by simp) (by scalar_tac)

/-- Generalized spec for `from_fn_aux`: every index of the result satisfies
`P`, given that the closure does and that the accumulator already does. -/
theorem core.array.from_fn_aux_spec
    {T F : Type} [Inhabited T] (N : Usize)
    (call : F → Usize → Result (T × F))
    (P : Nat → T → Prop)
    (hcall : ∀ f' (j : Usize), j.val < N.val →
      call f' j ⦃ (val, _) => P j.val val ⦄)
    (f : F) (i : Nat) (acc : List T)
    (hacc : acc.length = i) (hi : i ≤ N.val)
    (hpre : ∀ j, j < i → P j acc[j]!) :
    core.array.from_fn_aux N call f i acc hacc hi
      ⦃ (arr : Array T N) => ∀ j, j < N.val → P j arr.val[j]! ⦄ := by
  unfold core.array.from_fn_aux
  simp only [WP.spec, WP.theta]
  split
  · rename_i hlt
    have hspec := hcall f (Usize.ofNatCore i (by scalar_tac)) (by scalar_tac)
    simp only [WP.spec, WP.theta] at hspec
    revert hspec; cases call f (Usize.ofNatCore i (by scalar_tac)) with
    | ok p =>
      simp only [WP.wp_return]; intro hP; simp only [bind_tc_ok]
      apply core.array.from_fn_aux_spec N call P hcall p.2 (i + 1) (acc ++ [p.1])
        (by simp [hacc]) (by scalar_tac)
      intro j hj
      by_cases hjlt : j < i
      · simp_lists [hacc]; exact hpre j hjlt
      · have : j = i := by scalar_tac
        subst this; simp [hacc]; exact hP
    | fail e => intro h; exact h
    | div => intro h; exact h
  · intro j hj; exact hpre j (by scalar_tac)

/-- State-tracking variant of `from_fn_aux_spec`. The per-index predicate
may depend on the *current* closure state; the call must preserve a
state invariant `inv` and `P` must be monotone under `inv`. Useful for
closures whose state evolves between calls. -/
theorem core.array.from_fn_aux_state_spec
    {T F : Type} [Inhabited T] (N : Usize)
    (call : F → Usize → Result (T × F))
    (inv : F → Prop)
    (P : F → Nat → T → Prop)
    (hcall : ∀ f' (j : Usize), j.val < N.val → inv f' →
      call f' j ⦃ (val, f'') => inv f'' ∧ P f' j.val val ⦄)
    (Pmono : ∀ f f' j v, inv f → inv f' → P f j v → P f' j v)
    (f : F) (hf : inv f) (i : Nat) (acc : List T)
    (hacc : acc.length = i) (hi : i ≤ N.val)
    (hpre : ∀ j, j < i → P f j acc[j]!) :
    core.array.from_fn_aux N call f i acc hacc hi
      ⦃ (arr : Array T N) => ∀ j, j < N.val → P f j arr.val[j]! ⦄ := by
  unfold core.array.from_fn_aux
  simp only [WP.spec, WP.theta]
  split
  · rename_i hlt
    have hspec := hcall f (Usize.ofNatCore i (by scalar_tac)) (by scalar_tac) hf
    simp only [WP.spec, WP.theta] at hspec
    revert hspec; cases call f (Usize.ofNatCore i (by scalar_tac)) with
    | ok p =>
      simp only [WP.wp_return]; intro ⟨hinv', hP⟩; simp only [bind_tc_ok]
      apply WP.spec_mono
      · apply core.array.from_fn_aux_state_spec N call inv P hcall Pmono p.2 hinv'
          (i + 1) (acc ++ [p.1]) (by simp [hacc]) (by scalar_tac)
        intro j hj
        by_cases hjlt : j < i
        · simp_lists [hacc]; exact Pmono f p.2 j _ hf hinv' (hpre j hjlt)
        · have hji : j = i := by scalar_tac
          rw [hji]; simp [hacc]
          have hP' : P f i p.1 := by
            have : (Usize.ofNatCore i (by scalar_tac) : Usize).val = i := by scalar_tac
            rw [← this]; exact hP
          exact Pmono f p.2 i p.1 hf hinv' hP'
      · intro arr hPnext j hj
        exact Pmono p.2 f j _ hinv' hf (hPnext j hj)
    | fail e => intro h; exact h
    | div => intro h; exact h
  · intro j hj; exact hpre j (by scalar_tac)

/-- Step spec for `core.array.from_fn`: each element of the result satisfies
`P`, provided the closure produces `P`-satisfying outputs at every index
regardless of accumulated state (covers stateless closures). -/
@[step]
theorem core.array.from_fn.step_spec
    {T F : Type} [Inhabited T] (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (f : F)
    (P : Nat → T → Prop)
    (hcall : ∀ f' (j : Usize), j.val < N.val →
      inst.call_mut f' j ⦃ (val, _) => P j.val val ⦄) :
    core.array.from_fn N inst f
      ⦃ (arr : Array T N) => ∀ j, j < N.val → P j arr.val[j]! ⦄ := by
  unfold core.array.from_fn
  exact core.array.from_fn_aux_spec N inst.call_mut P hcall f 0 [] (by simp)
    (by scalar_tac) (by intro j hj; scalar_tac)

end Aeneas.Std
