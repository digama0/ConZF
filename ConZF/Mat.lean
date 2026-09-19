import ConZF.PSet
/-
The materializing recursion (doc/main.tex, section 3). Paths are lists of labels, a type in
the same universe as `PSet`; targets are arbitrary sets; and the operation `D` (in the
application: `G ↦ V_{rank G + ω}`) is an arbitrary parameter.
-/
universe u

namespace PSet

/-- Labels of children: the child `a`, whose value `G` is computed first; the children
`b w` for `w ∈ D G`; and the children `c x` for `x` in a parameter set. -/
inductive Label : Type (u+1)
  | a
  | b (w : PSet.{u})
  | c (x : PSet.{u})

inductive Label.Equiv : Label.{u} → Label.{u} → Prop
  | a : Label.Equiv .a .a
  | b {w w'} : w ≈ w' → Label.Equiv (.b w) (.b w')
  | c {x x'} : x ≈ x' → Label.Equiv (.c x) (.c x')

/-- A path, deepest label first. The carrier of the recursion; it lives in `Type (u+1)`,
the same universe as `PSet.{u}`. -/
abbrev Path := List Label.{u}

variable (D : PSet.{u} → PSet.{u}) (U : PSet.{u})

section step
variable (R : Path.{u} → Path.{u} → Prop) (p : Path.{u})
  (rec : (c : Path.{u}) → R c p → PSet.{u})

/-- A guarded recursive call: `succ (rec (l :: p))` if `l :: p` is below `p`, else `∅`. -/
def call (l : Label.{u}) : PSet.{u} := guard (R (l :: p) p) fun h => succ (rec (l :: p) h)

/-- The value of the first call, or `∅`. -/
def stepG : PSet.{u} := guard (R (.a :: p) p) fun h => rec (.a :: p) h

/-- The step of the recursion. The second family of calls is indexed by the index type of
`D G`, where `G` is the value of the first call. -/
def step : PSet.{u} :=
  union (call R p rec .a) <| union
    (iUnion fun i : (D (stepG R p rec)).Idx => call R p rec (.b ((D (stepG R p rec)).Func i)))
    (iUnion fun j : U.Idx => call R p rec (.c (U.Func j)))

end step

/-- The materializing recursion: `Acc`-recursion on the big carrier `Path`, with motive
the big type `PSet`. -/
def F (R : Path.{u} → Path.{u} → Prop) (p : Path.{u}) (acc : Acc R p) : PSet.{u} :=
  Acc.rec (motive := fun _ _ => PSet.{u}) (fun p _ ih => step D U R p ih) acc

theorem F_eq (R) (p : Path.{u}) (acc : Acc R p) :
    F D U R p acc = step D U R p fun c h => F D U R c (acc.inv h) := by
  cases acc; rfl

/-! ### Target assignments -/

/-- The relation of a target assignment: `c` is a child of `p` and has a target. -/
def Rel (τ : Path.{u} → PSet.{u} → Prop) (c p : Path.{u}) : Prop :=
  ∃ l, c = l :: p ∧ ∃ t, τ c t

/-- `G` is the target of the child `a` of `p`, or empty if there is none. -/
def IsG (τ : Path.{u} → PSet.{u} → Prop) (p : Path.{u}) (G : PSet.{u}) : Prop :=
  ∀ x, x ∈ G ↔ ¬¬∃ ζ, τ (.a :: p) ζ ∧ x ∈ ζ

/-- The labels the step enumerates when the first call returns `G`. -/
def Avail (G : PSet.{u}) (l : Label.{u}) : Prop :=
  l = .a ∨ (∃ w, w ∈ D G ∧ l.Equiv (.b w)) ∨ ∃ x, x ∈ U ∧ l.Equiv (.c x)

/-- A coherent target assignment. It is a proposition about a relation; no part of it is
data. All conditions are stable. -/
structure Coherent (τ : Path.{u} → PSet.{u} → Prop) : Prop where
  /-- targets are determined up to bisimulation -/
  resp : ∀ {p t t'}, τ p t → t ≈ t' → τ p t'
  func : ∀ {p t t'}, τ p t → τ p t' → t ≈ t'
  /-- the assignment does not see the representation of a label -/
  lab : ∀ {l l' p t}, Label.Equiv l l' → τ (l :: p) t → τ (l' :: p) t
  /-- the target of a child is an element of the target of its parent -/
  desc : ∀ {l p t t'}, τ (l :: p) t → τ p t' → t ∈ t'
  /-- a target is the union of the successors of the targets of the available children -/
  sup : ∀ {p t G}, τ p t → IsG τ p G →
    ∀ x, x ∈ t ↔ ¬¬∃ l t', Avail D U G l ∧ τ (l :: p) t' ∧ x ∈ succ t'

variable {D U}

/-- What the step computes, given that the recursive calls return the targets. -/
theorem mem_step_iff {τ : Path.{u} → PSet.{u} → Prop} (hτ : Coherent D U τ) {p : Path.{u}}
    {rec : (c : Path.{u}) → Rel τ c p → PSet.{u}}
    (hrec : ∀ c h t, τ c t → rec c h ≈ t) (x : PSet.{u}) :
    x ∈ step D U (Rel τ) p rec ↔
      ¬¬∃ l t', Avail D U (stepG (Rel τ) p rec) l ∧ τ (l :: p) t' ∧ x ∈ succ t' := by
  have hcall : ∀ l, x ∈ call (Rel τ) p rec l ↔ ¬¬∃ t', τ (l :: p) t' ∧ x ∈ succ t' := by
    intro l
    refine mem_guard.trans ⟨nn_map ?_, nn_map ?_⟩
    · rintro ⟨h, hx⟩
      have ⟨_, _, t', ht'⟩ := h
      exact ⟨t', ht', (mem_congr_right (succ_congr (hrec _ h _ ht'))).1 hx⟩
    · rintro ⟨t', ht', hx⟩
      have h : Rel τ (l :: p) p := ⟨l, rfl, t', ht'⟩
      exact ⟨h, (mem_congr_right (succ_congr (hrec _ h _ ht'))).2 hx⟩
  constructor
  · intro h
    refine Stable.of_nn (mem_union.1 h) fun h => ?_
    rcases h with h | h
    · exact nn_map (fun ⟨t', h1, h2⟩ => ⟨_, t', .inl rfl, h1, h2⟩) ((hcall _).1 h)
    refine Stable.of_nn (mem_union.1 h) fun h => ?_
    rcases h with h | h
    · refine Stable.of_nn (mem_iUnion.1 h) fun ⟨i, h⟩ => ?_
      exact nn_map (fun ⟨t', h1, h2⟩ =>
        ⟨_, t', .inr (.inl ⟨_, func_mem _ i, .b (Equiv.refl _)⟩), h1, h2⟩) ((hcall _).1 h)
    · refine Stable.of_nn (mem_iUnion.1 h) fun ⟨j, h⟩ => ?_
      exact nn_map (fun ⟨t', h1, h2⟩ =>
        ⟨_, t', .inr (.inr ⟨_, func_mem _ j, .c (Equiv.refl _)⟩), h1, h2⟩) ((hcall _).1 h)
  · intro h
    refine Stable.of_nn h ?_
    rintro ⟨l, t', hl | ⟨w, hw, hl⟩ | ⟨y, hy, hl⟩, h1, h2⟩
    · subst hl
      exact mem_union.2 (nn_intro (.inl ((hcall _).2 (nn_intro ⟨t', h1, h2⟩))))
    · refine hw.elim fun i e => ?_
      refine mem_union.2 (nn_intro (.inr (mem_union.2 (nn_intro (.inl
        (mem_iUnion.2 (nn_intro ⟨i, (hcall _).2 (nn_intro ⟨t', ?_, h2⟩)⟩)))))))
      cases hl with | b hl => exact hτ.lab (.b (hl.trans e)) h1
    · refine hy.elim fun j e => ?_
      refine mem_union.2 (nn_intro (.inr (mem_union.2 (nn_intro (.inr
        (mem_iUnion.2 (nn_intro ⟨j, (hcall _).2 (nn_intro ⟨t', ?_, h2⟩)⟩)))))))
      cases hl with | c hl => exact hτ.lab (.c (hl.trans e)) h1

theorem isG_stepG {τ : Path.{u} → PSet.{u} → Prop} {p : Path.{u}}
    {rec : (c : Path.{u}) → Rel τ c p → PSet.{u}}
    (hrec : ∀ c h t, τ c t → rec c h ≈ t) : IsG τ p (stepG (Rel τ) p rec) := by
  refine fun x => mem_guard.trans ⟨nn_map ?_, nn_map ?_⟩
  · rintro ⟨h, hx⟩
    have ⟨_, _, ζ, hζ⟩ := h
    exact ⟨ζ, hζ, (mem_congr_right (hrec _ h _ hζ)).1 hx⟩
  · rintro ⟨ζ, hζ, hx⟩
    have h : Rel τ (.a :: p) p := ⟨_, rfl, ζ, hζ⟩
    exact ⟨h, (mem_congr_right (hrec _ h _ hζ)).2 hx⟩

/-- **Materialization, the value.** If `τ` is coherent and `p` has the target `t`, then the
recursion returns `t` at `p`, whatever the accessibility proof. No excluded middle. -/
theorem materialize {τ : Path.{u} → PSet.{u} → Prop} (hτ : Coherent D U τ) :
    ∀ (t : PSet.{u}) (p : Path.{u}), τ p t → ∀ acc, F D U (Rel τ) p acc ≈ t := by
  intro t
  refine mem_induction t fun t ih => ?_
  intro p hp acc
  have hrec : ∀ c (h : Rel τ c p) tc, τ c tc → F D U (Rel τ) c (acc.inv h) ≈ tc := by
    rintro c ⟨l, rfl, _⟩ tc htc
    exact ih tc (hτ.desc htc hp) _ htc _
  refine ext fun x => ?_
  rw [F_eq]
  exact (mem_step_iff hτ hrec _).trans (hτ.sup hp (isG_stepG hrec) _).symm

/-! ### Accessibility

Accessibility is not a stable proposition, and membership induction is only available for
stable predicates. What can be proved is that the relation of an assignment with the descent
condition is well-founded *for stable predicates* (`swf_root_of_desc` below). -/

/-- `p` is in the well-founded part of `R` as far as stable predicates can tell. -/
def SWF {α : Sort _} (R : α → α → Prop) (p : α) : Prop :=
  ∀ P : α → Prop, (∀ x, Stable (P x)) → (∀ x, (∀ y, R y x → P y) → P x) → P p

/-! ### Accessibility from the well-foundedness of membership

The carrier of the recursion has to be the type of paths, because a step must produce its
children as terms and the targets are not terms. But the *accessibility* of a path does not
depend on the paths: it follows from the accessibility of its target under membership, by the
descent condition alone. -/

/-- The descent condition of a target assignment. -/
def Desc (τ : Path.{u} → PSet.{u} → Prop) : Prop := ∀ {l p t t'}, τ (l :: p) t → τ p t' → t ∈ t'

theorem acc_of_desc {τ : Path.{u} → PSet.{u} → Prop} (desc : Desc τ) {t : PSet.{u}}
    (ht : Acc (· ∈ ·) t) : ∀ p, τ p t → Acc (Rel τ) p := by
  induction ht with
  | intro t _ ih =>
    intro p hp
    exact ⟨_, fun c ⟨_, e, tc, htc⟩ => by subst e; exact ih tc (desc htc hp) _ htc⟩

/-- If membership is well-founded, every root is accessible. -/
theorem acc_root_of_desc {τ : Path.{u} → PSet.{u} → Prop} (desc : Desc τ)
    (wf : ∀ x : PSet.{u}, Acc (· ∈ ·) x) : Acc (Rel τ) [] :=
  ⟨_, fun c ⟨_, _, tc, htc⟩ => acc_of_desc desc (wf tc) c htc⟩

theorem swf_root_of_desc {τ : Path.{u} → PSet.{u} → Prop} (desc : Desc τ) : SWF (Rel τ) [] := by
  intro P hs H
  have := hs
  have key : ∀ (t : PSet.{u}) (p : Path.{u}), τ p t → P p := fun t =>
    mem_induction t fun t ih p hp => H p <| by
      rintro c ⟨l, rfl, tc, htc⟩
      exact ih tc (desc htc hp) _ htc
  exact H [] fun c ⟨_, _, tc, htc⟩ => key tc c htc
