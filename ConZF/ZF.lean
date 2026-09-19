import ConZF.Proof
/-!
`ZF` as a first-order theory: extensionality, foundation, pairing, union, power set, infinity,
and the schemas of separation and replacement. Free variables of an axiom are parameters. The
replacement schema is in its usual form "a functional relation on `a` has its values in some
`b`"; with separation this gives the image.

`ZFModel M` lists closure conditions on a class of sets which make every axiom valid in it.
-/
universe u

namespace PSet
open Fml

namespace ZFAx

/-- `∀z (z ∈ x ↔ z ∈ y) → x = y` -/
def ext : Fml := imp (all (iff (mem 0 1) (mem 0 2))) (eq 0 1)

/-- `∃z z ∈ x → ∃y (y ∈ x ∧ ∀z (z ∈ y → z ∉ x))` -/
def found : Fml :=
  imp (ex (mem 0 1)) (ex (and (mem 0 1) (all (imp (mem 0 1) (neg (mem 0 2))))))

/-- `∃z (x ∈ z ∧ y ∈ z)` -/
def pair : Fml := ex (and (mem 1 0) (mem 2 0))

/-- `∃u ∀y ∀z (z ∈ y → y ∈ x → z ∈ u)` -/
def union : Fml := ex (all (all (imp (mem 0 1) (imp (mem 1 3) (mem 0 2)))))

/-- `∃p ∀y (∀z (z ∈ y → z ∈ x) → y ∈ p)` -/
def power : Fml := ex (all (imp (all (imp (mem 0 1) (mem 0 3))) (mem 0 1)))

/-- `∃w (∃e (e ∈ w ∧ ∀z z ∉ e) ∧ ∀y (y ∈ w → ∃s (s ∈ w ∧ ∀z (z ∈ s ↔ z ∈ y ∨ z = y))))` -/
def inf : Fml :=
  ex (and (ex (and (mem 0 1) (all (neg (mem 0 1)))))
    (all (imp (mem 0 1) (ex (and (mem 0 2) (all (iff (mem 0 1) (or (mem 0 2) (eq 0 2)))))))))

def sepR : Nat → Nat
  | 0 => 0
  | n+1 => n+2

/-- `∃y ∀z (z ∈ y ↔ z ∈ x ∧ ψ(z, params))`, where `ψ` has `z` as variable `0` and the free
variables of the axiom (`x` among them) as its variables `n+1`. -/
def sep (ψ : Fml) : Fml := ex (all (iff (mem 0 1) (and (mem 0 2) (rename sepR ψ))))

def r1 : Nat → Nat
  | 0 => 2
  | 1 => 1
  | n+2 => n+3

def r2 : Nat → Nat
  | 0 => 2
  | 1 => 0
  | n+2 => n+3

def r3 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => n+3

/-- `∀x (x ∈ a → ∀y ∀y' (ψ(x,y) → ψ(x,y') → y = y')) → ∃b ∀y (∃x (x ∈ a ∧ ψ(x,y)) → y ∈ b)`,
where `ψ` has `x`, `y` as variables `0`, `1` and the free variables of the axiom (`a` among
them) as its variables `n+2`. -/
def repl (ψ : Fml) : Fml :=
  imp (all (imp (mem 0 1) (all (all (imp (rename r1 ψ) (imp (rename r2 ψ) (eq 1 0)))))))
    (ex (all (imp (ex (and (mem 0 3) (rename r3 ψ))) (mem 0 1))))

end ZFAx

/-- The axioms of `ZF`. -/
inductive ZF : Fml → Prop
  | ext : ZF ZFAx.ext
  | found : ZF ZFAx.found
  | pair : ZF ZFAx.pair
  | union : ZF ZFAx.union
  | power : ZF ZFAx.power
  | inf : ZF ZFAx.inf
  | sep (ψ : Fml) : ZF (ZFAx.sep ψ)
  | repl (ψ : Fml) : ZF (ZFAx.repl ψ)

/-- Closure conditions on a class which make it a model of `ZF`. Existence is doubly negated,
as everywhere in the stable reading. -/
structure ZFModel (M : PSet.{u} → Prop) : Prop where
  trans : ∀ {x z}, M x → z ∈ x → M z
  empty : M empty
  upair : ∀ {x y}, M x → M y → M (upair x y)
  sUnion : ∀ {x}, M x → M (sUnion x)
  powerset : ∀ {x}, M x → M (powerset x)
  omega : M omega
  sep : ∀ (P : PSet.{u} → Prop) {x}, M x → M (sep P x)
  repl : ∀ (ψ : Fml) (e : Nat → PSet.{u}), (∀ i, M (e i)) → ∀ a, M a →
    (∀ x y y', x ∈ a → M y → M y' → Sat M ψ (Env.cons x (Env.cons y e)) →
      Sat M ψ (Env.cons x (Env.cons y' e)) → y ≈ y') →
    ¬¬∃ b, M b ∧ ∀ x y, x ∈ a → M y → Sat M ψ (Env.cons x (Env.cons y e)) → y ∈ b

/-- Every nonempty subset of a set has an `∈`-minimal element. -/
theorem exists_minimal (x : PSet.{u}) (z) :
    z ∈ x → ¬¬∃ y, y ∈ x ∧ ∀ w, w ∈ y → ¬ w ∈ x :=
  mem_induction z fun z ih hz =>
    Stable.by_cases (∃ w, w ∈ z ∧ w ∈ x) (fun ⟨w, hw, hwx⟩ => ih w hw hwx)
      fun h => nn_intro ⟨z, hz, fun w hw hwx => h ⟨w, hw, hwx⟩⟩

namespace ZFModel
variable {M : PSet.{u} → Prop} (hM : ZFModel M)
include hM

theorem valid : ∀ φ, ZF φ → Valid M φ := by
  intro φ h e he
  cases h with
  | ext =>
    intro h
    exact ext fun z =>
      ⟨fun hz => (sat_iff.1 (h z (hM.trans (he 0) hz))).1 hz,
       fun hz => (sat_iff.1 (h z (hM.trans (he 1) hz))).2 hz⟩
  | found =>
    intro h
    refine Stable.of_nn (sat_ex.1 h) fun ⟨z, _, hz⟩ => ?_
    refine Stable.of_nn (exists_minimal (e 0) z hz) fun ⟨y, hy, hmin⟩ => ?_
    exact sat_ex.2 (nn_intro ⟨y, hM.trans (he 0) hy,
      sat_and.2 ⟨hy, fun w _ hw hwx => hmin w hw hwx⟩⟩)
  | pair =>
    exact sat_ex.2 (nn_intro ⟨PSet.upair (e 0) (e 1), hM.upair (he 0) (he 1),
      sat_and.2 ⟨mem_upair_left _ _, mem_upair_right _ _⟩⟩)
  | union =>
    exact sat_ex.2 (nn_intro ⟨PSet.sUnion (e 0), hM.sUnion (he 0),
      fun y _ z _ hz hy => mem_sUnion.2 (nn_intro ⟨y, hy, hz⟩)⟩)
  | power =>
    exact sat_ex.2 (nn_intro ⟨PSet.powerset (e 0), hM.powerset (he 0),
      fun y hy h => mem_powerset.2 fun z hz => h z (hM.trans hy hz) hz⟩)
  | inf =>
    refine sat_ex.2 (nn_intro ⟨PSet.omega, hM.omega, sat_and.2 ⟨?_, fun y _ hy => ?_⟩⟩)
    · exact sat_ex.2 (nn_intro ⟨PSet.empty, hM.empty,
        sat_and.2 ⟨ofNat_mem_omega 0, fun z _ hz => not_mem_empty z hz⟩⟩)
    · refine Stable.of_nn (mem_omega.1 hy) fun ⟨n, e'⟩ => ?_
      refine sat_ex.2 (nn_intro ⟨ofNat (n+1), hM.trans hM.omega (ofNat_mem_omega (n+1)),
        sat_and.2 ⟨ofNat_mem_omega (n+1), fun z _ => sat_iff.2 ?_⟩⟩)
      refine mem_succ.trans <| .trans (nn_congr ?_) sat_or.symm
      exact or_congr (mem_congr_right e').symm ⟨fun h => h.trans e'.symm, fun h => h.trans e'⟩
  | sep ψ =>
    let P : PSet.{u} → Prop := fun z => Sat M ψ (Env.cons z e)
    have hP : ∀ z z' : PSet.{u}, z ≈ z' → P z → P z' := fun _ _ ez h =>
      Sat.resp ψ (Env.cons_resp ez fun _ => Equiv.refl _) h
    have : ∀ z, Stable (P z) := fun z => Sat.stable ψ _
    refine sat_ex.2 (nn_intro ⟨PSet.sep P (e 0), hM.sep P (he 0), fun z _ => sat_iff.2 ?_⟩)
    have hPz : P z ↔ Sat M (rename ZFAx.sepR ψ) (Env.cons z (Env.cons (PSet.sep P (e 0)) e)) :=
      .trans (Sat.resp_iff (fun _ => Iff.rfl) ψ fun i => by cases i <;> exact Equiv.refl _)
        (sat_rename ψ ZFAx.sepR _).symm
    refine (mem_sep hP).trans ⟨fun ⟨a, b⟩ => sat_and.2 ⟨a, hPz.1 b⟩, fun h => ?_⟩
    have ⟨a, b⟩ := sat_and.1 h
    exact ⟨a, hPz.2 b⟩
  | repl ψ =>
    intro hf
    have R2 : ∀ {x y y'}, Sat M ψ (Env.cons x (Env.cons y' e)) →
        Sat M (rename ZFAx.r2 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) := fun h =>
      (sat_rename ψ ZFAx.r2 _).2
        (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _) h)
    have R1' : ∀ {x y y'}, Sat M ψ (Env.cons x (Env.cons y e)) →
        Sat M (rename ZFAx.r1 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) := fun h =>
      (sat_rename ψ ZFAx.r1 _).2
        (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _) h)
    refine Stable.of_nn (hM.repl ψ e he (e 0) (he 0) fun x y y' hx hy hy' h1 h2 =>
      hf x (hM.trans (he 0) hx) hx y hy y' hy' (R1' (y' := y') h1) (R2 (y := y) h2))
      fun ⟨b, hb, hb'⟩ => ?_
    refine sat_ex.2 (nn_intro ⟨b, hb, fun y hy h => ?_⟩)
    refine Stable.of_nn (sat_ex.1 h) fun ⟨x, _, hx⟩ => ?_
    have ⟨hxa, hs⟩ := sat_and.1 hx
    exact hb' x y hxa hy (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _)
      ((sat_rename ψ ZFAx.r3 _).1 hs))

theorem con : Con ZF := Con.of_model hM.valid PSet.empty hM.empty
