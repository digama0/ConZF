import ConZF.PSet
/-!
Ordinals and rank, in the stable reading. Statements with a disjunction or an existential are
doubly negated; they are used through `Stable.of_nn` when proving stable goals. No excluded
middle is assumed anywhere.
-/
universe u

namespace PSet

theorem mem_asymm (x : PSet.{u}) : ∀ {{y}}, y ∈ x → ¬ x ∈ y :=
  mem_induction x fun _ ih _ hy hx => ih _ hy hx hy

theorem not_mem_self (a : PSet.{u}) : ¬ a ∈ a := fun h => mem_asymm a h h

theorem succ_inj {t t' : PSet.{u}} (h : succ t ≈ succ t') : t ≈ t' := by
  have h1 : t ∈ succ t' := (mem_congr_right h).1 (self_mem_succ t)
  have h2 : t' ∈ succ t := (mem_congr_right h).2 (self_mem_succ t')
  refine Stable.of_nn (mem_succ.1 h1) fun h1 => Stable.of_nn (mem_succ.1 h2) fun h2 => ?_
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact (mem_asymm _ h1 h2).elim
    · exact h2.symm
  · exact h1

def Trans (t : PSet.{u}) : Prop := ∀ y, y ∈ t → ∀ z, z ∈ y → z ∈ t

instance {t : PSet.{u}} : Stable (Trans t) :=
  inferInstanceAs (Stable (∀ y, y ∈ t → ∀ z, z ∈ y → z ∈ t))

/-- Von Neumann ordinals: transitive sets of transitive sets (foundation is built in). -/
structure IsOrd (t : PSet.{u}) : Prop where
  trans : Trans t
  mem_trans : ∀ y, y ∈ t → Trans y

instance {t : PSet.{u}} : Stable (IsOrd t) :=
  ⟨fun h => ⟨Stable.dne fun hn => h fun h => hn h.1, Stable.dne fun hn => h fun h => hn h.2⟩⟩

theorem Trans.resp {t t' : PSet.{u}} (e : t ≈ t') (h : Trans t) : Trans t' :=
  fun y hy z hz => (mem_congr_right e).1 (h y ((mem_congr_right e).2 hy) z hz)

theorem IsOrd.resp {t t' : PSet.{u}} (e : t ≈ t') (h : IsOrd t) : IsOrd t' :=
  ⟨h.trans.resp e, fun y hy => h.mem_trans y ((mem_congr_right e).2 hy)⟩

theorem IsOrd.mem {t y : PSet.{u}} (h : IsOrd t) (hy : y ∈ t) : IsOrd y :=
  ⟨h.mem_trans y hy, fun z hz => h.mem_trans z (h.trans y hy z hz)⟩

theorem isOrd_empty : IsOrd empty.{u} :=
  ⟨fun _ h => (not_mem_empty _ h).elim, fun _ h => (not_mem_empty _ h).elim⟩

theorem IsOrd.succ {t : PSet.{u}} (h : IsOrd t) : IsOrd (succ t) := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · refine Stable.of_nn (mem_succ.1 hy) fun hy => ?_
    rcases hy with hy | e
    · exact mem_succ_of_mem (h.trans y hy z hz)
    · exact mem_succ_of_mem ((mem_congr_right e).1 hz)
  · refine Stable.of_nn (mem_succ.1 hy) fun hy => ?_
    rcases hy with hy | e
    · exact h.mem_trans y hy
    · exact h.trans.resp e.symm

theorem isOrd_iUnion {ι : Type u} {A : ι → PSet.{u}} (h : ∀ i, IsOrd (A i)) : IsOrd (iUnion A) := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · exact Stable.of_nn (mem_iUnion.1 hy) fun ⟨i, hi⟩ =>
      mem_iUnion.2 (nn_intro ⟨i, (h i).trans y hi z hz⟩)
  · exact Stable.of_nn (mem_iUnion.1 hy) fun ⟨i, hi⟩ => (h i).mem_trans y hi

/-- Ordinals are linearly ordered by `∈`. -/
theorem IsOrd.trichotomy : ∀ {{a b : PSet.{u}}}, IsOrd a → IsOrd b → ¬¬(a ∈ b ∨ a ≈ b ∨ b ∈ a) := by
  refine fun a => mem_induction a fun a iha b => mem_induction b fun b ihb ha hb => ?_
  refine Stable.by_cases (a ∈ b) (fun h => nn_intro (.inl h)) fun h1 => ?_
  refine Stable.by_cases (b ∈ a) (fun h => nn_intro (.inr (.inr h))) fun h2 => ?_
  refine nn_intro (.inr (.inl (ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)))
  · refine Stable.of_nn (iha z hz (ha.mem hz) hb) fun h => ?_
    rcases h with h | h | h
    · exact h
    · exact (h2 ((mem_congr_left h).1 hz)).elim
    · exact (h2 (ha.trans z hz b h)).elim
  · refine Stable.of_nn (ihb z hz ha (hb.mem hz)) fun h => ?_
    rcases h with h | h | h
    · exact (h1 (hb.trans z hz a h)).elim
    · exact (h1 ((mem_congr_left h).2 hz)).elim
    · exact h

/-- For ordinals, inclusion is `∈` or `≈`. -/
theorem IsOrd.subset {a b : PSet.{u}} (ha : IsOrd a) (hb : IsOrd b) (h : ∀ z, z ∈ a → z ∈ b) :
    ¬¬(a ∈ b ∨ a ≈ b) :=
  nn_map (fun
    | .inl h' => .inl h'
    | .inr (.inl h') => .inr h'
    | .inr (.inr h') => (not_mem_self b (h b h')).elim) (ha.trichotomy hb)

theorem IsOrd.mem_succ_of_subset {a b : PSet.{u}} (ha : IsOrd a) (hb : IsOrd b)
    (h : ∀ z, z ∈ a → z ∈ b) : a ∈ PSet.succ b :=
  mem_succ.2 (ha.subset hb h)

/-! ### Rank -/

def rank : PSet.{u} → PSet.{u}
  | ⟨_, A⟩ => iUnion fun a => succ (rank (A a))

theorem mem_rank {x z : PSet.{u}} : z ∈ rank x ↔ ¬¬∃ a, z ∈ succ (rank (x.Func a)) := by
  cases x; exact mem_iUnion

theorem rank_congr : ∀ {x y : PSet.{u}}, x ≈ y → rank x ≈ rank y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨h1, h2⟩ => ext fun _ =>
    ⟨fun h => Stable.of_nn (mem_iUnion.1 h) fun ⟨a, h⟩ => Stable.of_nn (h1 a) fun ⟨b, e⟩ =>
       mem_iUnion.2 (nn_intro ⟨b, (mem_congr_right (succ_congr (rank_congr e))).1 h⟩),
     fun h => Stable.of_nn (mem_iUnion.1 h) fun ⟨b, h⟩ => Stable.of_nn (h2 b) fun ⟨a, e⟩ =>
       mem_iUnion.2 (nn_intro ⟨a, (mem_congr_right (succ_congr (rank_congr e))).2 h⟩)⟩

/-- `z ∈ rank x` iff `z ≤ rank y` for some `y ∈ x`. -/
theorem mem_rank' {x z : PSet.{u}} : z ∈ rank x ↔ ¬¬∃ y, y ∈ x ∧ z ∈ succ (rank y) :=
  mem_rank.trans ⟨nn_map fun ⟨a, h⟩ => ⟨_, func_mem x a, h⟩,
    fun h => nn_bind h fun ⟨_, hy, h⟩ => nn_map (fun ⟨a, e⟩ =>
      ⟨a, (mem_congr_right (succ_congr (rank_congr e))).1 h⟩) hy⟩

theorem rank_mem {x y : PSet.{u}} (h : y ∈ x) : rank y ∈ rank x :=
  mem_rank'.2 (nn_intro ⟨y, h, self_mem_succ _⟩)

theorem isOrd_rank : ∀ x : PSet.{u}, IsOrd (rank x)
  | ⟨_, A⟩ => isOrd_iUnion fun a => (isOrd_rank (A a)).succ

/-- The rank of an ordinal is itself. -/
theorem IsOrd.rank_equiv {t : PSet.{u}} : IsOrd t → rank t ≈ t := by
  refine mem_induction t fun t ih ht => ?_
  refine ext fun z => mem_rank'.trans ⟨fun h => ?_, fun hz => nn_intro ⟨z, hz, ?_⟩⟩
  · refine Stable.of_nn h fun ⟨y, hy, hz⟩ => ?_
    refine Stable.of_nn (mem_succ.1 ((mem_congr_right (succ_congr (ih y hy (ht.mem hy)))).1 hz)) ?_
    rintro (hz | e)
    · exact ht.trans y hy z hz
    · exact (mem_congr_left e).2 hy
  · exact (mem_congr_right (succ_congr (ih z hz (ht.mem hz)))).2 (self_mem_succ z)

/-- If every element of `y` has rank below the ordinal `R`, then `rank y ≤ R`. -/
theorem rank_mem_succ {y R : PSet.{u}} (hR : IsOrd R) (h : ∀ z, z ∈ y → rank z ∈ R) :
    rank y ∈ succ R := by
  refine (isOrd_rank y).mem_succ_of_subset hR fun w hw => ?_
  refine Stable.of_nn (mem_rank'.1 hw) fun ⟨z, hz, hw⟩ => ?_
  refine Stable.of_nn (mem_succ.1 hw) ?_
  rintro (hw | e)
  · exact hR.trans _ (h z hz) w hw
  · exact (mem_congr_left e).2 (h z hz)
