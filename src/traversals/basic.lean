import algebraic_topology.simplicial_set
import category_theory.limits.has_limits
import category_theory.functor_category
import category_theory.limits.yoneda
import category_theory.limits.presheaf
import simplicial_sets.simplex_as_hom

open category_theory
open category_theory.limits
open simplex_category
open sSet
open_locale simplicial

/-!
# Traversals
Defines n-traversals, pointed n-traversals and their corresponding simplicial sets.

## Notations
* `∔` for a plus,
* `∸` for a minus,
* `e :: θ` for adding an edge e at the start of a traversal θ,
* `e ⬝ α` for the action of a map α on an edge e,
* `θ ⬝ α` for the action of a map α on a traversal θ.
-/

namespace traversal

@[derive decidable_eq]
inductive pm
| plus  : pm
| minus : pm

notation `±` := pm
notation `∔` := pm.plus
notation `∸` := pm.minus

@[reducible]
def edge (n : ℕ) := fin (n+1) × ±

def edge.lt {n} : edge n → edge n → Prop
| (i, ∸) (j, ∸) := i < j
| (i, ∸) (j, ∔) := true
| (i, ∔) (j, ∸) := false
| (i, ∔) (j, ∔) := j < i

instance {n} : has_lt (edge n) := ⟨edge.lt⟩

instance edge.has_decidable_lt {n} : Π e₁ e₂ : edge n, decidable (e₁ < e₂)
| (i, ∸) (j, ∸) := fin.decidable_lt i j
| (i, ∸) (j, ∔) := is_true trivial
| (i, ∔) (j, ∸) := is_false not_false
| (i, ∔) (j, ∔) := fin.decidable_lt j i

lemma edge.lt_asymm {n} : Π e₁ e₂ : edge n, e₁ < e₂ → e₂ < e₁ → false
| (i, ∸) (j, ∸) := nat.lt_asymm
| (i, ∸) (j, ∔) := λ h₁ h₂, h₂
| (i, ∔) (j, ∸) := λ h₁ h₂, h₁
| (i, ∔) (j, ∔) := nat.lt_asymm

instance {n} : is_asymm (edge n) edge.lt := ⟨edge.lt_asymm⟩

end traversal

@[reducible]
def traversal (n : ℕ) := list (traversal.edge n)

@[reducible]
def pointed_traversal (n : ℕ) := traversal n × traversal n

namespace traversal

notation h :: t  := list.cons h t
notation `⟦` l:(foldr `, ` (h t, list.cons h t) list.nil `⟧`) := (l : traversal _)

instance decidable_mem {n} :
  Π (e : edge n) (θ : traversal n), decidable (e ∈ θ) := list.decidable_mem


@[reducible]
def sorted {n} (θ : traversal n) := list.sorted edge.lt θ

theorem eq_of_sorted_of_same_elem {n : ℕ} : Π (θ₁ θ₂ : traversal n) (s₁ : sorted θ₁) (s₂ : sorted θ₂),
  (Π e, e ∈ θ₁ ↔ e ∈ θ₂) → θ₁ = θ₂
| ⟦⟧         ⟦⟧         := λ _ _ _, rfl
| ⟦⟧         (e₂ :: t₂) := λ _ _ H, begin exfalso, simpa using H e₂, end
| (e₁ :: t₁) ⟦⟧         := λ _ _ H, begin exfalso, simpa using H e₁, end
| (e₁ :: t₁) (e₂ :: t₂) := λ s₁ s₂ H,
begin
  simp only [sorted, list.sorted_cons] at s₁ s₂,
  cases s₁ with he₁ ht₁,
  cases s₂ with he₂ ht₂,
  have he₁e₂ : e₁ = e₂,
  { have He₁ := H e₁, simp at He₁, cases He₁ with heq He₁, from heq,
    have He₂ := H e₂, simp at He₂, cases He₂ with heq He₂, from heq.symm,
    exfalso, exact edge.lt_asymm e₁ e₂ (he₁ e₂ He₂) (he₂ e₁ He₁), },
  cases he₁e₂, simp,
  { apply eq_of_sorted_of_same_elem t₁ t₂ ht₁ ht₂,
    intro e, specialize H e, simp at H, split,
    { intro he,
      cases H.1 (or.intro_right _ he) with h, cases h,
      exfalso, exact edge.lt_asymm e₁ e₁ (he₁ e₁ he) (he₁ e₁ he),
      exact h, },
    { intro he,
      cases H.2 (or.intro_right _ he) with h, cases h,
      exfalso, exact edge.lt_asymm e₁ e₁ (he₂ e₁ he) (he₂ e₁ he),
      exact h, }}
end

theorem append_sorted {n : ℕ} : Π (θ₁ θ₂ : traversal n) (s₁ : sorted θ₁) (s₂ : sorted θ₂),
  (∀ (e₁ ∈ θ₁) (e₂ ∈ θ₂), e₁ < e₂) → sorted (θ₁ ++ θ₂)
| ⟦⟧         θ₂ := λ _ s₂ _, s₂
| (e₁ :: t₁) θ₂ := λ s₁ s₂ H,
begin
  simp only [sorted, list.sorted_cons] at s₁ s₂ ⊢,
  cases s₁ with he₁ ht₁,
  dsimp, rw list.sorted_cons,
  split,
  { intros e he, simp at he, cases he,
    exact he₁ e he,
    refine H e₁ (list.mem_cons_self e₁ t₁) e he },
  { apply append_sorted t₁ θ₂ ht₁ s₂,
    intros e₁' he₁' e₂' he₂',
    refine H e₁' (list.mem_cons_of_mem e₁ he₁') e₂' he₂' }
end

theorem append_sorted_iff {n : ℕ} : Π (θ₁ θ₂ : traversal n),
  sorted θ₁ ∧ sorted θ₂ ∧ (∀ (e₁ ∈ θ₁) (e₂ ∈ θ₂), e₁ < e₂) ↔ sorted (θ₁ ++ θ₂)
| ⟦⟧         θ₂ := by simp[sorted, list.sorted_nil]
| (e₁ :: t₁) θ₂ :=
begin
  split, rintro ⟨s₁, s₂, H⟩, apply append_sorted _ _ s₁ s₂ H,
  intro H, dsimp[sorted] at H, rw list.sorted_cons at H,
  change _ ∧ sorted _ at H, rw ←append_sorted_iff at H,
  split,
  { dsimp[sorted], rw list.sorted_cons, split,
    intros b hb, exact H.1 b (list.mem_append_left θ₂ hb),
    exact H.2.1 },
  split, exact H.2.2.1,
  intros e' he', simp at he', cases he', cases he',
  intros e₂ he₂, exact H.1 e₂ (list.mem_append_right t₁ he₂),
  exact H.2.2.2 e' he',
end

/-! # Applying a map to an edge -/

def apply_map_to_plus {n m : simplex_category} (i : fin (n.len+1)) (α : m ⟶ n) :
  Π (j : ℕ), j < m.len+1 → traversal m.len
| 0       h0  := if α.to_preorder_hom 0 = i then ⟦⟨0, ∔⟩⟧ else ⟦⟧
| (j + 1) hj  :=
  if α.to_preorder_hom ⟨j+1,hj⟩ = i
  then (⟨j+1, hj⟩, ∔) :: (apply_map_to_plus j (nat.lt_of_succ_lt hj))
  else apply_map_to_plus j (nat.lt_of_succ_lt hj)

lemma min_notin_apply_map_to_plus {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) (j : ℕ) (hj : j < m.len + 1) :
  ∀ (k : fin (m.len + 1)), (k, ∸) ∉ apply_map_to_plus i α j hj :=
begin
  intros k hk,
  induction j with j,
  { simp [apply_map_to_plus] at hk,
    split_ifs at hk; simp at hk; exact hk },
  { simp [apply_map_to_plus] at hk,
    split_ifs at hk, simp at hk,
    repeat {exact j_ih _ hk }}
end

lemma plus_in_apply_map_to_plus_iff {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) (j : ℕ) (hj : j < m.len + 1) :
  ∀ (k : fin (m.len + 1)), (k, ∔) ∈ apply_map_to_plus i α j hj ↔ k.val < j + 1 ∧ α.to_preorder_hom k = i :=
begin
  intros k,
  induction j with j,
  { simp only [apply_map_to_plus], split_ifs; simp, split,
    intro hk, cases hk, simp, exact h,
    intro hk, ext, simp, linarith,
    intro hk, replace hk : k = 0, ext, simp, linarith, cases hk, exact h, },
  { simp only [apply_map_to_plus], split_ifs; simp; rw j_ih; simp,
    split, intro hk, cases hk, cases hk, split, simp, exact h,
    split, exact nat.le_succ_of_le hk.1, exact hk.2,
    intro hk, rw hk.2, simp, cases nat.of_le_succ hk.1, right, exact h_1, left, ext, simp, exact nat.succ.inj h_1,
    intro hk, split, intro hkj, exact nat.le_succ_of_le hkj,
    intro hkj, cases nat.of_le_succ hkj, exact h_1,
    exfalso, have H : k = ⟨j + 1, hj⟩, ext, exact nat.succ.inj h_1, cases H, exact h hk, }
end

lemma apply_map_to_plus_sorted {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) (j : ℕ) (hj : j < m.len + 1) :
  sorted (apply_map_to_plus i α j hj) :=
begin
  dsimp [sorted],
  induction j with j,
  { simp [apply_map_to_plus],
    split_ifs; simp, },
  { simp [apply_map_to_plus],
    split_ifs, swap, exact j_ih (nat.lt_of_succ_lt hj),
    simp only [list.sorted_cons], split, swap, exact j_ih (nat.lt_of_succ_lt hj),
    intros e he, cases e with k, cases e_snd,
    rw plus_in_apply_map_to_plus_iff at he, exact he.1,
    exact absurd he (min_notin_apply_map_to_plus α i j _ k), },
end

def apply_map_to_min {n m : simplex_category} (i : fin (n.len+1)) (α : m ⟶ n) :
Π (j : ℕ), j < m.len+1 → traversal m.len
| 0       h0  := if α.to_preorder_hom m.last = i then ⟦⟨m.last, ∸⟩⟧ else ⟦⟧
| (j + 1) hj  :=
  if α.to_preorder_hom ⟨m.len-(j+1), nat.sub_lt_succ _ _⟩ = i
  then (⟨m.len-(j+1), nat.sub_lt_succ _ _⟩, ∸) :: (apply_map_to_min j (nat.lt_of_succ_lt hj))
  else apply_map_to_min j (nat.lt_of_succ_lt hj)

lemma plus_notin_apply_map_to_min {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) (j : ℕ) (hj : j < m.len + 1) :
  ∀ (k : fin (m.len + 1)), (k, ∔) ∉ apply_map_to_min i α j hj :=
begin
  intros k hk,
  induction j with j,
  { simp [apply_map_to_min] at hk,
    split_ifs at hk; simp at hk; exact hk },
  { simp [apply_map_to_min] at hk,
    split_ifs at hk, simp at hk,
    repeat {exact j_ih _ hk }}
end

lemma min_in_apply_map_to_min_iff {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) (j : ℕ) (hj : j < m.len + 1) :
  ∀ (k : fin (m.len + 1)), (k, ∸) ∈ apply_map_to_min i α j hj ↔ k.val ≥ m.len - j ∧ α.to_preorder_hom k = i :=
begin
  intros k,
  induction j with j,
  { simp only [apply_map_to_min], split_ifs; simp, split,
    intro hk, cases hk, simp, split, refl, exact h,
    intro hk, ext, exact le_antisymm (fin.le_last k) hk.1,
    intro hk, replace hk : k = m.last, ext, exact le_antisymm (fin.le_last k) hk,
    cases hk, exact h, },
  {
    have Hk : ∀ k, m.len - j.succ ≤ k ↔ m.len - j ≤ k ∨ m.len - j.succ = k,
    { have hmj_pos : 0 < m.len - j, from nat.sub_pos_of_lt (nat.succ_lt_succ_iff.mp hj),
      rw nat.lt_succ_iff at hj, intro k,
      rw [nat.sub_succ, ←nat.succ_le_succ_iff, ←nat.succ_inj', nat.succ_pred_eq_of_pos hmj_pos],
      exact nat.le_add_one_iff, },
    simp only [apply_map_to_min], split_ifs; simp; rw j_ih; simp,
    split, intro hk, cases hk, cases hk, split, simp, exact h,
    split, rw nat.sub_succ, exact nat.le_trans (nat.pred_le _) hk.1, exact hk.2,
    intro hk, rw hk.2, simp, cases (Hk k).mp hk.1, right, exact h_1, left, ext, exact h_1.symm,
    intro hk, rw Hk k, split, intro hkj, left, exact hkj,
    intro hkj, cases hkj, exact hkj,
    have Hk' : k = ⟨m.len - (j + 1), apply_map_to_min._main._proof_1 _⟩, ext, exact hkj.symm,
    cases Hk', exact absurd hk h,}
end

lemma apply_map_to_min_sorted {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) (j : ℕ) (hj : j < m.len + 1) :
  list.sorted edge.lt (apply_map_to_min i α j hj) :=
begin
  induction j with j,
  { simp [apply_map_to_min],
    split_ifs; simp, },
  { simp [apply_map_to_min],
    split_ifs, swap, exact j_ih (nat.lt_of_succ_lt hj),
    simp only [list.sorted_cons], split, swap, exact j_ih (nat.lt_of_succ_lt hj),
    intros e he, cases e with k, cases e_snd,
    exact absurd he (plus_notin_apply_map_to_min α i j _ k),
    rw min_in_apply_map_to_min_iff at he,
    replace he : k.val ≥ m.len - j := he.1,
    change m.len - (j + 1) < k.val,
    refine lt_of_lt_of_le _ he, rw nat.sub_succ,
    refine nat.pred_lt _, simp,
    rwa [nat.sub_eq_zero_iff_le, not_le, ←nat.succ_lt_succ_iff], },
end

def apply_map_to_edge {n m : simplex_category} (α : m ⟶ n) : edge n.len → traversal m.len
| (i, ∔) := apply_map_to_plus i α m.last.1 m.last.2
| (i, ∸) := apply_map_to_min i α m.last.1 m.last.2

notation e ⬝ α := apply_map_to_edge α e

example (p : Prop) (h : p) : p ↔ true := iff_of_true h trivial

@[simp]
lemma edge_in_apply_map_to_edge_iff {n m : simplex_category} (α : m ⟶ n) :
  ∀ (e₁ : edge m.len) (e₂), e₁ ∈ e₂ ⬝ α ↔ (α.to_preorder_hom e₁.1, e₁.2) = e₂ :=
begin
  intros e₁ e₂, cases e₁ with i₁ b₁, cases e₂ with i₂ b₂,
  cases b₁; cases b₂; simp [apply_map_to_edge],
  { simp [plus_in_apply_map_to_plus_iff],
    exact λ _, i₁.2, },
  { apply plus_notin_apply_map_to_min, },
  { apply min_notin_apply_map_to_plus, },
  { simp [min_in_apply_map_to_min_iff, simplex_category.last], },
end

lemma apply_map_to_edge_sorted {n m : simplex_category} (α : m ⟶ n) :
  ∀ (e : edge n.len), sorted (e ⬝ α)
| (i, ∔) := apply_map_to_plus_sorted α i _ _
| (i, ∸) := apply_map_to_min_sorted α i _ _

/-! # Applying a map to a traversal -/

def apply_map {n m : simplex_category} (α : m ⟶ n) : traversal n.len → traversal m.len
| ⟦⟧       := ⟦⟧
| (e :: t) := (e ⬝ α) ++ apply_map t

notation θ ⬝ α := apply_map α θ

@[simp]
lemma edge_in_apply_map_iff {n m : simplex_category} (α : m ⟶ n) (θ : traversal n.len) :
  ∀ (e : edge m.len), e ∈ θ ⬝ α ↔ (α.to_preorder_hom e.1, e.2) ∈ θ :=
begin
  intros e, induction θ;
  simp [apply_map, list.mem_append],
  simp [edge_in_apply_map_to_edge_iff, θ_ih],
end

def apply_map_preserves_sorted {n m : simplex_category} (α : m ⟶ n) (θ : traversal n.len) :
  sorted θ → sorted (θ ⬝ α) :=
begin
  intro sθ, induction θ; dsimp [sorted, apply_map],
  { exact list.sorted_nil },
  simp only [sorted, list.sorted_cons] at sθ,
  apply append_sorted,
  apply apply_map_to_edge_sorted,
  apply θ_ih sθ.2,
  intros e₁ he₁ e₂ he₂,
  rw edge_in_apply_map_to_edge_iff at he₁,
  rw edge_in_apply_map_iff at he₂,
  replace sθ := sθ.1 (α.to_preorder_hom e₂.fst, e₂.snd) he₂,
  cases he₁, clear he₁ he₂,
  cases e₁ with i₁ b₁, cases e₂ with i₂ b₂,
  cases b₁; cases b₂; simp [edge.lt] at sθ ⊢;
  try {change i₂ < i₁}; try {trivial}; try {change i₁ < i₂};
  rw ←not_le at sθ ⊢;
  exact λ H, sθ (α.to_preorder_hom.monotone H),
end

@[simp]
lemma apply_map_append {n m : simplex_category} (α : m ⟶ n) : Π (θ₁ θ₂ : traversal n.len),
  apply_map α (θ₁ ++ θ₂) = (apply_map α θ₁) ++ (apply_map α θ₂)
| ⟦⟧ θ₂        := rfl
| (h :: θ₁) θ₂ :=
begin
  dsimp[apply_map],
  rw apply_map_append,
  rw list.append_assoc,
end

@[simp]
lemma apply_id {n : simplex_category} : ∀ (θ : traversal n.len), apply_map (𝟙 n) θ = θ
| ⟦⟧       := rfl
| (e :: θ) :=
begin
  unfold apply_map,
  rw [apply_id θ], change _ = ⟦e⟧ ++ θ,
  rw list.append_left_inj,
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_to_edge_sorted },
  { exact list.sorted_singleton e },
  { intro e, simp }
end

@[simp]
lemma apply_comp {n m l : simplex_category} (α : m ⟶ n) (β : n ⟶ l) :
  ∀ (θ : traversal l.len), apply_map (α ≫ β) θ = apply_map α (apply_map β θ)
| ⟦⟧       := rfl
| (e :: θ) :=
begin
  unfold apply_map,
  rw [apply_map_append, ←apply_comp, list.append_left_inj],
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_to_edge_sorted },
  { apply apply_map_preserves_sorted,
    apply apply_map_to_edge_sorted },
  { intro e, simp, }
end

/-! # The application of the standard face maps and standard degeneracies. -/

@[simp] lemma apply_δ_self {n} (i : fin (n + 2)) (b : ±) :
  apply_map_to_edge (δ i) (i, b) = ⟦⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  apply apply_map_to_edge_sorted,
  exact list.sorted_nil,
  intro e, cases e, simp,
  intro h, exfalso,
  simp [δ, fin.succ_above] at h,
  split_ifs at h,
  finish,
  rw [not_lt, fin.le_cast_succ_iff] at h_1, finish,
end

@[simp] lemma apply_δ_succ_cast_succ {n} (i : fin (n + 1)) (b : ±) :
  apply_map_to_edge (δ i.succ) (i.cast_succ, b) = ⟦(i, b)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  apply apply_map_to_edge_sorted,
  exact list.sorted_singleton (i, b),
  intro e, cases e, simp,
  intro hb, cases hb,
  split,
  { intro he,
    have H : (δ i.succ ≫ σ i).to_preorder_hom e_fst = (σ i).to_preorder_hom i.cast_succ,
    { rw ←he, simp, },
    rw δ_comp_σ_succ at H,
    simpa [σ, fin.pred_above] using H, },
  { intro he, cases he,
    simp [δ, fin.succ_above, fin.cast_succ_lt_succ], }
end

@[simp] lemma apply_δ_cast_succ_succ {n} (i : fin (n + 1)) (b : ±) :
  apply_map_to_edge (δ i.cast_succ) (i.succ, b) = ⟦(i, b)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  apply apply_map_to_edge_sorted,
  exact list.sorted_singleton (i, b),
  intro e, cases e, simp,
  intro hb, cases hb,
  split,
  { intro he,
    have H : (δ i.cast_succ ≫ σ i).to_preorder_hom e_fst = (σ i).to_preorder_hom i.succ,
    { rw ←he, simp, },
    rw δ_comp_σ_self at H,
    simp [σ, fin.pred_above] at H,
    split_ifs at H, from H,
    exact absurd (fin.cast_succ_lt_succ i) h, },
  { intro he, cases he,
    simp [δ, fin.succ_above, fin.cast_succ_lt_succ], }
end

@[simp] lemma apply_σ_to_plus {n} (i : fin (n + 1)) :
  apply_map_to_edge (σ i) (i, ∔) = ⟦(i.succ, ∔), (i.cast_succ, ∔)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_to_edge_sorted,},
  { simp [sorted], intros a b ha hb, rw ha, rw hb,
    exact fin.cast_succ_lt_succ i, },
  { intro e, cases e with l b,
    rw edge_in_apply_map_to_edge_iff,
    simp, rw ←or_and_distrib_right, simp, intro hb, clear hb b,
    simp [σ, fin.pred_above],
    split,
    { intro H, split_ifs at H,
      rw ←fin.succ_inj at H, simp at H,
      left, exact H,
      rw ←fin.cast_succ_inj at H, simp at H,
      right, exact H, },
    { intro H, cases H; rw H; simp[fin.cast_succ_lt_succ], }}
end

@[simp] lemma apply_σ_to_min {n} (i : fin (n + 1)) :
  apply_map_to_edge (σ i) (i, ∸) = ⟦(i.cast_succ, ∸), (i.succ, ∸)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_to_edge_sorted, },
  { simp[sorted],
    intros a b ha hb, rw [ha, hb],
    exact fin.cast_succ_lt_succ i, },
  { intro e, cases e with l b,
    rw edge_in_apply_map_to_edge_iff,
    simp, rw ←or_and_distrib_right, simp, intro hb, clear hb b,
    simp [σ, fin.pred_above],
    split,
    { intro H, split_ifs at H,
      rw ←fin.succ_inj at H, simp at H,
      right, exact H,
      rw ←fin.cast_succ_inj at H, simp at H,
      left, exact H, },
    { intro H, cases H; rw H; simp[fin.cast_succ_lt_succ], }}
end

def edge.s {n} : edge n → fin (n+2)
| ⟨k, ∔⟩ := k.succ
| ⟨k, ∸⟩ := k.cast_succ

def edge.t {n} : edge n → fin (n+2)
| ⟨k, ∔⟩ := k.cast_succ
| ⟨k, ∸⟩ := k.succ

notation e`ˢ` := e.s
notation e`ᵗ` := e.t

lemma apply_σ_to_self {n} (e : edge n) :
  apply_map_to_edge (σ e.1) e = ⟦(eˢ, e.2), (eᵗ, e.2)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_to_edge_sorted, },
  { dsimp [sorted],
    rw [list.sorted_cons],
    split, swap, apply list.sorted_singleton,
    intro e', simp, intro he', cases he',
    cases e with i b, cases b;
    exact fin.cast_succ_lt_succ i },
  { intro e', simp,
    cases e with i b, cases i with i hi,
    cases e' with i' b', cases i' with i' hi',
    cases b; cases b';
    simp [σ, fin.pred_above, edge.s, edge.t];
    split_ifs;
    try { rw ←fin.succ_inj, simp [h] };
    split; intro hi;
    cases hi;
    try { linarith };
    simp }
end

/- Simplicial set of traversals. -/
def 𝕋₀ : sSet :=
{ obj       := λ n, traversal n.unop.len,
  map       := λ x y α, apply_map α.unop,
  map_id'   := λ n, funext (λ θ, apply_id θ),
  map_comp' := λ l n m β α, funext (λ θ, apply_comp α.unop β.unop θ) }

lemma 𝕋₀_map_apply {n m : simplex_categoryᵒᵖ} {f : n ⟶ m} {θ : traversal n.unop.len} :
  𝕋₀.map f θ = θ.apply_map f.unop := rfl

/- Simplicial set of pointed traversals. -/
def 𝕋₁ : sSet :=
{ obj       := λ x, pointed_traversal x.unop.len,
  map       := λ _ _ α θ, (𝕋₀.map α θ.1, 𝕋₀.map α θ.2),
  map_id'   := λ _, by ext1 θ; simp,
  map_comp' := λ _ _ _ _ _, by ext1 θ; simp }

@[simp] lemma 𝕋₁_map_apply {n m : simplex_categoryᵒᵖ} {f : n ⟶ m} {θ₁ θ₂ : traversal n.unop.len} :
  𝕋₁.map f (θ₁, θ₂) = (𝕋₀.map f θ₁, 𝕋₀.map f θ₂) := rfl

@[simp] lemma 𝕋₁_map_apply_fst {n m : simplex_categoryᵒᵖ} {f : n ⟶ m} {θ : pointed_traversal n.unop.len} :
  (𝕋₁.map f θ).1 = 𝕋₀.map f θ.1 := rfl

@[simp] lemma 𝕋₁_map_apply_snd {n m : simplex_categoryᵒᵖ} {f : n ⟶ m} {θ : pointed_traversal n.unop.len} :
  (𝕋₁.map f θ).2 = 𝕋₀.map f θ.2 := rfl

def dom : 𝕋₁ ⟶ 𝕋₀ :=
{ app         := λ n θ, θ.2,
  naturality' := λ n m α, rfl }

def cod : 𝕋₁ ⟶ 𝕋₀ :=
{ app         := λ n θ, list.append θ.1 θ.2,
  naturality' := λ m m α, funext (λ θ, (traversal.apply_map_append α.unop θ.1 θ.2).symm) }

def as_hom {n} (θ : traversal n) : Δ[n] ⟶ 𝕋₀ := simplex_as_hom θ

end traversal

def pointed_traversal.as_hom {n} (θ : pointed_traversal n) :
  Δ[n] ⟶ traversal.𝕋₁ := simplex_as_hom θ
