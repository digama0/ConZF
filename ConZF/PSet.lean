import ConZF.Logic
/-
Sets as trees (Aczel), from scratch in Lean core, in the negative translation: bisimulation
and membership use `¬¬∃` at every level, so every statement about sets is stable and may be
proved classically, without excluded middle. Nothing here uses any axiom.
-/
universe u

/-- `V = W X : Type u. X`. -/
inductive PSet : Type (u+1)
  | mk (α : Type u) (A : α → PSet) : PSet

namespace PSet

def Idx : PSet.{u} → Type u | ⟨α, _⟩ => α
def Func : (x : PSet.{u}) → x.Idx → PSet.{u} | ⟨_, A⟩ => A

/-- Bisimulation, negatively. -/
def Equiv : PSet.{u} → PSet.{u} → Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (∀ a, ¬¬∃ b, Equiv (A a) (B b)) ∧ (∀ b, ¬¬∃ a, Equiv (A a) (B b))

infixl:50 " ≈ " => Equiv

instance Equiv.stable : {x y : PSet.{u}} → Stable (x ≈ y)
  | ⟨_, _⟩, ⟨_, _⟩ => inferInstanceAs (Stable (_ ∧ _))

theorem Equiv.refl : (x : PSet.{u}) → x ≈ x
  | ⟨_, A⟩ => ⟨fun a => nn_intro ⟨a, Equiv.refl (A a)⟩, fun a => nn_intro ⟨a, Equiv.refl (A a)⟩⟩

theorem Equiv.symm : {x y : PSet.{u}} → x ≈ y → y ≈ x
  | ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩ =>
    ⟨fun b => nn_map (fun ⟨a, h⟩ => ⟨a, h.symm⟩) (h2 b),
     fun a => nn_map (fun ⟨b, h⟩ => ⟨b, h.symm⟩) (h1 a)⟩

theorem Equiv.trans : {x y z : PSet.{u}} → x ≈ y → y ≈ z → x ≈ z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩, ⟨k1, k2⟩ =>
    ⟨fun a => nn_bind (h1 a) fun ⟨b, h⟩ => nn_map (fun ⟨c, k⟩ => ⟨c, h.trans k⟩) (k1 b),
     fun c => nn_bind (k2 c) fun ⟨b, k⟩ => nn_map (fun ⟨a, h⟩ => ⟨a, h.trans k⟩) (h2 b)⟩

/-- Membership, negatively. -/
def Mem (x y : PSet.{u}) : Prop := ¬¬∃ b, x ≈ y.Func b

instance : Membership PSet.{u} PSet.{u} := ⟨fun y x => Mem x y⟩

instance {x y : PSet.{u}} : Stable (x ∈ y) := inferInstanceAs (Stable (¬_))

theorem mem_def {x y : PSet.{u}} : x ∈ y ↔ ¬¬∃ b, x ≈ y.Func b := Iff.rfl

theorem func_mem (y : PSet.{u}) (b : y.Idx) : y.Func b ∈ y := nn_intro ⟨b, Equiv.refl _⟩

theorem mem_congr_left {x x' y : PSet.{u}} (h : x ≈ x') : x ∈ y ↔ x' ∈ y :=
  ⟨nn_map fun ⟨b, e⟩ => ⟨b, h.symm.trans e⟩, nn_map fun ⟨b, e⟩ => ⟨b, h.trans e⟩⟩

theorem ext : {x y : PSet.{u}} → (∀ z, z ∈ x ↔ z ∈ y) → x ≈ y
  | ⟨_, A⟩, ⟨_, B⟩, H =>
    ⟨fun a => (H (A a)).1 (func_mem ⟨_, A⟩ a),
     fun b => nn_map (fun ⟨a, e⟩ => ⟨a, e.symm⟩) ((H (B b)).2 (func_mem ⟨_, B⟩ b))⟩

theorem mem_congr_right : {x y y' : PSet.{u}} → y ≈ y' → (x ∈ y ↔ x ∈ y')
  | _, ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩ =>
    ⟨fun h => nn_bind h fun ⟨a, ea⟩ => nn_map (fun ⟨b, eb⟩ => ⟨b, ea.trans eb⟩) (h1 a),
     fun h => nn_bind h fun ⟨b, eb⟩ => nn_map (fun ⟨a, ea⟩ => ⟨a, eb.trans ea.symm⟩) (h2 b)⟩

theorem equiv_iff_mem {x y : PSet.{u}} : x ≈ y ↔ ∀ z, z ∈ x ↔ z ∈ y :=
  ⟨fun h _ => mem_congr_right h, ext⟩

/-- `∈`-induction, for **stable** predicates. -/
@[elab_as_elim] theorem mem_induction {P : PSet.{u} → Prop} [∀ x, Stable (P x)]
    (x : PSet.{u}) (H : ∀ x, (∀ y, y ∈ x → P y) → P x) : P x := by
  suffices ∀ x y, y ≈ x → P y from this x x (Equiv.refl x)
  intro x
  induction x with
  | mk α A ih =>
    intro y hy
    refine H y fun z hz => Stable.of_nn ((mem_congr_right hy).1 hz) fun ⟨a, e⟩ => ih a z e

/-- To use `z ∈ x` for a stable goal, one may assume an index. -/
theorem Mem.elim {g : Prop} [Stable g] {z x : PSet.{u}} (h : z ∈ x)
    (f : ∀ b, z ≈ x.Func b → g) : g :=
  Stable.of_nn h fun ⟨b, e⟩ => f b e

/-! ### Operations -/

def empty : PSet.{u} := ⟨PEmpty, PEmpty.elim⟩

theorem not_mem_empty (x : PSet.{u}) : ¬ x ∈ empty := fun h => h fun ⟨b, _⟩ => b.elim

/-- The set `{A i | i : ι}` of a family indexed by a small type. -/
def range {ι : Type u} (A : ι → PSet.{u}) : PSet.{u} := ⟨ι, A⟩

theorem mem_range {ι : Type u} {A : ι → PSet.{u}} {x} : x ∈ range A ↔ ¬¬∃ i, x ≈ A i := Iff.rfl

def sUnion (a : PSet.{u}) : PSet.{u} :=
  ⟨Σ x : a.Idx, (a.Func x).Idx, fun p => (a.Func p.1).Func p.2⟩

theorem mem_sUnion {a x : PSet.{u}} : x ∈ sUnion a ↔ ¬¬∃ y, y ∈ a ∧ x ∈ y :=
  ⟨nn_map fun ⟨⟨i, j⟩, e⟩ => ⟨a.Func i, func_mem _ _, nn_intro ⟨j, e⟩⟩,
   fun h => nn_bind h fun ⟨_, hy, hx⟩ => nn_bind hy fun ⟨i, e⟩ =>
    nn_map (fun ⟨j, e'⟩ => ⟨⟨i, j⟩, e'⟩) ((mem_congr_right e).1 hx)⟩

/-- `⋃ i, A i` for a family indexed by a small type. -/
def iUnion {ι : Type u} (A : ι → PSet.{u}) : PSet.{u} := sUnion (range A)

theorem mem_iUnion {ι : Type u} {A : ι → PSet.{u}} {x} : x ∈ iUnion A ↔ ¬¬∃ i, x ∈ A i :=
  mem_sUnion.trans
    ⟨fun h => nn_bind h fun ⟨_, hy, hx⟩ => nn_map (fun ⟨i, e⟩ => ⟨i, (mem_congr_right e).1 hx⟩) hy,
     nn_map fun ⟨i, hx⟩ => ⟨A i, func_mem (range A) i, hx⟩⟩

/-- The union of a family indexed by the proofs of a proposition: `t` if `P` holds, `∅` if not.
This is what replaces a decision procedure for `P`. -/
def guard (P : Prop) (t : P → PSet.{u}) : PSet.{u} :=
  iUnion (ι := ULift.{u} (PLift P)) fun h => t h.down.down

theorem mem_guard {P : Prop} {t : P → PSet.{u}} {x} : x ∈ guard P t ↔ ¬¬∃ h : P, x ∈ t h :=
  mem_iUnion.trans ⟨nn_map fun ⟨h, hx⟩ => ⟨h.down.down, hx⟩, nn_map fun ⟨h, hx⟩ => ⟨⟨⟨h⟩⟩, hx⟩⟩

def union (a b : PSet.{u}) : PSet.{u} :=
  iUnion (ι := ULift.{u} Bool) fun i => if i.down then a else b

theorem mem_union {a b x : PSet.{u}} : x ∈ union a b ↔ ¬¬(x ∈ a ∨ x ∈ b) :=
  mem_iUnion.trans
    ⟨nn_map fun
      | ⟨⟨true⟩, h⟩ => .inl h
      | ⟨⟨false⟩, h⟩ => .inr h,
     nn_map fun
      | .inl h => ⟨⟨true⟩, h⟩
      | .inr h => ⟨⟨false⟩, h⟩⟩

def singleton (a : PSet.{u}) : PSet.{u} := range (ι := PUnit) fun _ => a

theorem mem_singleton {a x : PSet.{u}} : x ∈ singleton a ↔ x ≈ a :=
  ⟨fun h => Stable.of_nn h fun ⟨_, e⟩ => e, fun e => nn_intro ⟨⟨⟩, e⟩⟩

def succ (a : PSet.{u}) : PSet.{u} := union a (singleton a)

theorem mem_succ {a x : PSet.{u}} : x ∈ succ a ↔ ¬¬(x ∈ a ∨ x ≈ a) :=
  mem_union.trans ⟨nn_map (Or.imp_right mem_singleton.1), nn_map (Or.imp_right mem_singleton.2)⟩

theorem mem_succ_of_mem {a x : PSet.{u}} (h : x ∈ a) : x ∈ succ a := mem_succ.2 (nn_intro (.inl h))

theorem mem_succ_of_equiv {a x : PSet.{u}} (h : x ≈ a) : x ∈ succ a :=
  mem_succ.2 (nn_intro (.inr h))

theorem self_mem_succ (a : PSet.{u}) : a ∈ succ a := mem_succ_of_equiv (Equiv.refl a)

theorem succ_congr {a a' : PSet.{u}} (h : a ≈ a') : succ a ≈ succ a' :=
  ext fun _ => mem_succ.trans <| .trans
    ⟨nn_map (Or.imp (mem_congr_right h).1 fun e => e.trans h),
     nn_map (Or.imp (mem_congr_right h).2 fun e => e.trans h.symm)⟩ mem_succ.symm

/-- Separation, for a stable predicate. -/
def sep (p : PSet.{u} → Prop) (a : PSet.{u}) : PSet.{u} :=
  range (ι := {i : a.Idx // p (a.Func i)}) fun i => a.Func i.1

theorem mem_sep {p : PSet.{u} → Prop} [∀ x, Stable (p x)] (hp : ∀ x y, x ≈ y → p x → p y)
    {a x : PSet.{u}} : x ∈ sep p a ↔ x ∈ a ∧ p x :=
  ⟨fun h => Stable.of_nn h fun ⟨⟨i, h⟩, e⟩ => ⟨nn_intro ⟨i, e⟩, hp _ _ e.symm h⟩,
   fun ⟨h, hx⟩ => nn_map (fun ⟨i, e⟩ => ⟨⟨i, hp _ _ e hx⟩, e⟩) h⟩
