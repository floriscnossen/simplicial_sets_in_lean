import algebraic_topology.simplicial_set
import tactic.norm_fin
import contravariant_functor
import category_theory.limits.has_limits
import category_theory.functor_category

open category_theory
open category_theory.limits
open simplex_category
open sSet
open_locale simplicial

-- Maybe put these somewhere else

namespace simplex_category

def last (n : simplex_category) := fin.last n.len

end simplex_category

/-- Interpret a simplex as a morphism from a standard simplicial set. -/
def simplex_as_hom {n : ℕ} {X : sSet} (x : X.obj (opposite.op [n])) :
  Δ[n] ⟶ X :=
{ app := λ m f,
  begin
    change m.unop ⟶ [n] at f,
    exact X.map f.op x,
  end,
  naturality' := λ k m f,
  begin
    ext1 g, change k.unop ⟶ [n] at g, simp,
    rw [←types_comp_apply (X.map g.op) (X.map f), ←X.map_comp],
    apply congr_fun,
    apply congr_arg,
    refl,
  end
}

/-- Interpret a morphism in the simplex category as a morphism between standard simplicial sets. -/
def to_sSet_hom {n m} (f : [n] ⟶ [m]) : Δ[n] ⟶ Δ[m] := sSet.standard_simplex.map f

namespace traversal

inductive pm
| plus  : pm
| minus : pm

notation `±` := pm
notation `∔` := pm.plus
notation `∸` := pm.minus

@[reducible]
def edge (n : ℕ) := fin (n+1) × ±

def edge.lt {n} : edge n → edge n → Prop
| ⟨i, ∸⟩ ⟨j, ∸⟩ := i < j
| ⟨i, ∸⟩ ⟨j, ∔⟩ := true
| ⟨i, ∔⟩ ⟨j, ∸⟩ := false
| ⟨i, ∔⟩ ⟨j, ∔⟩ := j < i

instance {n} : has_lt (edge n) := ⟨edge.lt⟩

instance edge.has_decidable_lt {n} : Π e₁ e₂ : edge n, decidable (e₁ < e₂)
| ⟨i, ∸⟩ ⟨j, ∸⟩ := fin.decidable_lt i j
| ⟨i, ∸⟩ ⟨j, ∔⟩ := is_true trivial
| ⟨i, ∔⟩ ⟨j, ∸⟩ := is_false not_false
| ⟨i, ∔⟩ ⟨j, ∔⟩ := fin.decidable_lt j i

lemma edge.lt_asymm {n} : Π e₁ e₂ : edge n, e₁ < e₂ → e₂ < e₁ → false
| ⟨i, ∸⟩ ⟨j, ∸⟩ := nat.lt_asymm
| ⟨i, ∸⟩ ⟨j, ∔⟩ := λ h₁ h₂, h₂
| ⟨i, ∔⟩ ⟨j, ∸⟩ := λ h₁ h₂, h₁
| ⟨i, ∔⟩ ⟨j, ∔⟩ := nat.lt_asymm

instance {n} : is_asymm (edge n) edge.lt := ⟨edge.lt_asymm⟩

end traversal

@[reducible]
def traversal (n : ℕ) := list (traversal.edge n)

def pointed_traversal (n : ℕ) := traversal n × traversal n

namespace traversal

notation h :: t  := list.cons h t
notation `⟦` l:(foldr `, ` (h t, list.cons h t) list.nil `⟧`) := l

theorem eq_of_sorted_of_same_elem {n : ℕ} : Π (θ₁ θ₂ : traversal n) (s₁ : list.sorted edge.lt θ₁) (s₂ : list.sorted edge.lt θ₂),
  (Π e, e ∈ θ₁ ↔ e ∈ θ₂) → θ₁ = θ₂
| ⟦⟧         ⟦⟧         := λ _ _ _, rfl
| ⟦⟧         (e₂ :: t₂) := λ _ _ H, begin specialize H e₂, simp at H, exfalso, exact H, end
| (e₁ :: t₁) ⟦⟧         := λ _ _ H, begin specialize H e₁, simp at H, exfalso, exact H, end
| (e₁ :: t₁) (e₂ :: t₂) := λ s₁ s₂ H,
begin
  simp only [list.sorted_cons] at s₁ s₂,
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

-- theorem eq_of_same_elem' {n : ℕ} : Π (θ₁ θ₂ : traversal n) (s₁ : list.sorted (edge.has_lt.lt) θ₁) (s₂ : list.sorted edge.has_lt.lt θ₂),
--   (Π e, e ∈ θ₁ ↔ e ∈ θ₂) → θ₁ = θ₂ := λ θ₁ θ₂ s₁ s₂ H, begin library_search end

theorem append_sorted {n : ℕ} : Π (θ₁ θ₂ : traversal n) (s₁ : list.sorted edge.lt θ₁) (s₂ : list.sorted edge.lt θ₂),
  (Π e₁ e₂, e₁ ∈ θ₁ → e₂ ∈ θ₂ → e₁ < e₂) → list.sorted edge.lt (θ₁ ++ θ₂)
| ⟦⟧         θ₂ := λ _ s₂ _, s₂
| (e₁ :: t₁) θ₂ := λ s₁ s₂ H,
begin
  rw list.sorted_cons at s₁,
  cases s₁ with he₁ ht₁,
  dsimp, rw list.sorted_cons,
  split,
  { intros e he, simp at he, cases he,
    exact he₁ e he,
    refine H e₁ e (list.mem_cons_self e₁ t₁) he },
  { apply append_sorted t₁ θ₂ ht₁ s₂,
    intros e₁' e₂' he₁' he₂',
    refine H e₁' e₂' (list.mem_cons_of_mem e₁ he₁') he₂' }
end

def apply_map_to_plus {n m : simplex_category} (i : fin (n.len+1)) (α : m ⟶ n) :
  Π (j : ℕ), j < m.len+1 → traversal m.len
| 0       h0  := if α.to_preorder_hom 0 = i then ⟦⟨0, ∔⟩⟧ else ⟦⟧
| (j + 1) hj  :=
  if α.to_preorder_hom ⟨j+1,hj⟩ = i
  then ⟨⟨j+1,hj⟩, ∔⟩ :: (apply_map_to_plus j (nat.lt_of_succ_lt hj))
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

lemma plus_in_apply_map_to_plus_iff' {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) (j : ℕ) (hj : j < m.len + 1) :
  ∀ (k : fin (m.len + 1)), (k, ∔) ∈ apply_map_to_plus i α j hj ↔ k.val ≤ j ∧ α.to_preorder_hom k = i :=
begin
  intros k,
  induction j with j,
  { simp only [apply_map_to_plus], split_ifs; simp, split,
    intro hk, cases hk, simp, exact h,
    intro hk, ext, exact hk.1,
    intro hk, replace hk : k = 0, ext, exact hk, cases hk, exact h, },
  { simp only [apply_map_to_plus], split_ifs; simp; rw j_ih; simp,
    split, intro hk, cases hk, cases hk, split, simp, exact h,
    split, exact nat.le_succ_of_le hk.1, exact hk.2,
    intro hk, rw hk.2, simp, cases nat.of_le_succ hk.1, right, exact h_1, left, ext, simp, exact h_1,
    intro hk, split, intro hkj, exact nat.le_succ_of_le hkj,
    intro hkj, cases nat.of_le_succ hkj, exact h_1,
    exfalso, have H : k = ⟨j + 1, hj⟩, ext, exact h_1, cases H, exact h hk, }
end

lemma plus_in_apply_map_to_plus_iff {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) :
  ∀ (k : fin (m.len + 1)), (k, ∔) ∈ apply_map_to_plus i α m.len (nat.lt_succ_self m.len) ↔ α.to_preorder_hom k = i :=
begin
  intros k,
  rw [plus_in_apply_map_to_plus_iff', ←nat.lt_succ_iff],
  simp, exact λ h, k.2,
end

lemma apply_map_to_plus_sorted {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) (j : ℕ) (hj : j < m.len + 1) :
  list.sorted edge.lt (apply_map_to_plus i α j hj) :=
begin
  induction j with j,
  { simp [apply_map_to_plus],
    split_ifs; simp, },
  { simp [apply_map_to_plus],
    split_ifs, swap, exact j_ih (nat.lt_of_succ_lt hj),
    simp only [list.sorted_cons], split, swap, exact j_ih (nat.lt_of_succ_lt hj),
    intros e he, cases e with k, cases e_snd,
    rw plus_in_apply_map_to_plus_iff' at he,
    replace he : k.val ≤ j := he.1,
    rw ←nat.lt_succ_iff at he, exact he,
    exact absurd he (min_notin_apply_map_to_plus α i j _ k), },
end

lemma apply_id_to_plus {n : simplex_category} (i : fin (n.len+1)) :
  apply_map_to_plus i (𝟙 n) n.len (nat.lt_succ_self n.len) = ⟦⟨i, ∔⟩⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  apply apply_map_to_plus_sorted,
  apply list.sorted_singleton,
  rintro ⟨i, b⟩, cases b,
  rw plus_in_apply_map_to_plus_iff, simp,
  simp, apply min_notin_apply_map_to_plus,
end


def apply_map_to_min {n m : simplex_category} (i : fin (n.len+1)) (α : m ⟶ n) :
Π (j : ℕ), j < m.len+1 → traversal m.len
| 0       h0  := if α.to_preorder_hom m.last = i then ⟦⟨m.last, ∸⟩⟧ else ⟦⟧
| (j + 1) hj  :=
  if α.to_preorder_hom ⟨m.len-(j+1), nat.sub_lt_succ _ _⟩ = i
  then ⟨⟨m.len-(j+1), nat.sub_lt_succ _ _⟩, ∸⟩ :: (apply_map_to_min j (nat.lt_of_succ_lt hj))
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

lemma min_in_apply_map_to_min_iff' {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) (j : ℕ) (hj : j < m.len + 1) :
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

lemma min_in_apply_map_to_min_iff {n m : simplex_category} (α : m ⟶ n) (i : fin (n.len+1)) :
  ∀ (k : fin (m.len + 1)), (k, ∸) ∈ apply_map_to_min i α m.len (nat.lt_succ_self m.len) ↔ α.to_preorder_hom k = i :=
begin
  intros k, rw [min_in_apply_map_to_min_iff'], simp,
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
    rw min_in_apply_map_to_min_iff' at he,
    replace he : k.val ≥ m.len - j := he.1,
    change m.len - (j + 1) < k.val,
    refine lt_of_lt_of_le _ he, rw nat.sub_succ,
    refine nat.pred_lt _, simp,
    rwa [nat.sub_eq_zero_iff_le, not_le, ←nat.succ_lt_succ_iff], },
end

lemma apply_id_to_min {n : simplex_category} (i : fin (n.len+1)) :
  apply_map_to_min i (𝟙 n) n.len (nat.lt_succ_self n.len) = ⟦⟨i, ∸⟩⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  apply apply_map_to_min_sorted,
  apply list.sorted_singleton,
  rintro ⟨i, b⟩, cases b,
  simp, apply plus_notin_apply_map_to_min,
  rw min_in_apply_map_to_min_iff, simp,
end

def apply_map {n m : simplex_category} (α : m ⟶ n) : traversal n.len → traversal m.len
| ⟦⟧            := ⟦⟧
| (⟨i, ∔⟩ :: t) := (apply_map_to_plus i α m.len (nat.lt_succ_self m.len)) ++ apply_map t
| (⟨i, ∸⟩ :: t) := (apply_map_to_min i α m.len (nat.lt_succ_self m.len)) ++ apply_map t

lemma plus_in_apply_map_iff {n m : simplex_category} (α : m ⟶ n) (θ : traversal n.len) :
  ∀ k, (k, ∔) ∈ apply_map α θ ↔ (α.to_preorder_hom k, ∔) ∈ θ :=
begin
  intros k, induction θ,
  { simp [apply_map], },
  cases θ_hd with i, cases θ_hd_snd; simp [apply_map]; rw θ_ih,
  rw plus_in_apply_map_to_plus_iff,
  simp, intro hk, exfalso,
  exact plus_notin_apply_map_to_min α _ _ _ _ hk,
end

lemma min_in_apply_map_iff {n m : simplex_category} (α : m ⟶ n) (θ : traversal n.len) :
  ∀ k, (k, ∸) ∈ apply_map α θ ↔ (α.to_preorder_hom k, ∸) ∈ θ :=
begin
  intros k, induction θ,
  { simp [apply_map], },
  cases θ_hd with i, cases θ_hd_snd; simp [apply_map]; rw θ_ih,
  simp, intro hk, exfalso,
  exact min_notin_apply_map_to_plus α _ _ _ _ hk,
  rw min_in_apply_map_to_min_iff,
end

def apply_map_preserves_sorted {n m : simplex_category} (α : m ⟶ n) (θ : traversal n.len) :
  list.sorted edge.lt θ → list.sorted edge.lt (θ.apply_map α) :=
begin
  intro sθ, induction θ,
  { dsimp [apply_map], exact list.sorted_nil },
  specialize θ_ih (list.sorted_of_sorted_cons sθ),
  induction θ_hd with j, induction θ_hd_snd,
  { dsimp [apply_map],
    refine append_sorted _ _ (apply_map_to_plus_sorted α j m.len _) θ_ih _,
    rintros ⟨i₁, b₁⟩ ⟨i₂, b₂⟩ he₁ he₂,
    cases b₁, rw plus_in_apply_map_to_plus_iff at he₁, cases he₁,
    replace sθ := list.rel_of_sorted_cons sθ,
    cases b₂, rw plus_in_apply_map_iff at he₂,
    { change i₂ < i₁,
      have hlt : α.to_preorder_hom i₂ < α.to_preorder_hom i₁, from sθ _ he₂,
      exact not_le.mp (λ h, not_le.mpr hlt (α.to_preorder_hom.monotone h)), },
    { change false,
      rw min_in_apply_map_iff at he₂,
      exact sθ _ he₂ },
    { exact absurd he₁ (min_notin_apply_map_to_plus _ _ _ _ _) }},
  { dsimp [apply_map],
    refine append_sorted _ _ (apply_map_to_min_sorted α j m.len _) θ_ih _,
    rintros ⟨i₁, b₁⟩ ⟨i₂, b₂⟩ he₁ he₂,
    cases b₁,
    { exact absurd he₁ (plus_notin_apply_map_to_min _ _ _ _ _) },
    rw min_in_apply_map_to_min_iff at he₁, cases he₁,
    replace sθ := list.rel_of_sorted_cons sθ,
    cases b₂,
    { trivial, },
    { rw min_in_apply_map_iff at he₂,
      change i₁ < i₂,
      have hlt : α.to_preorder_hom i₁ < α.to_preorder_hom i₂, from sθ _ he₂,
      exact not_le.mp (λ h, not_le.mpr hlt (α.to_preorder_hom.monotone h)), },}
end

@[simp]
lemma map_id {n : simplex_category} : apply_map (𝟙 n) = 𝟙 (traversal n.len) :=
begin
  ext1 θ, change apply_map (𝟙 n) θ = θ,
  induction θ, refl, induction θ_hd, induction θ_hd_snd;
  unfold apply_map; rw θ_ih,
  { have H : (θ_hd_fst, ∔) :: θ_tl = ⟦(θ_hd_fst, ∔)⟧ ++ θ_tl, refl, rw H, clear H,
    rw list.append_left_inj,
    exact apply_id_to_plus θ_hd_fst, },
  { have H : (θ_hd_fst, ∸) :: θ_tl = ⟦(θ_hd_fst, ∸)⟧ ++ θ_tl, refl, rw H,
    rw list.append_left_inj,
    exact apply_id_to_min θ_hd_fst, },
end

@[simp]
lemma apply_map_append {n m : simplex_category} (α : m ⟶ n) (θ₁ θ₂ : traversal n.len) :
  apply_map α (θ₁ ++ θ₂) = (apply_map α θ₁) ++ (apply_map α θ₂) :=
begin
  induction θ₁, refl, induction θ₁_hd, induction θ₁_hd_snd,
  all_goals { simp, unfold apply_map, rw θ₁_ih, simp },
end

@[simp]
lemma comp_apply {n m l : simplex_category} (α : m ⟶ n) (β : n ⟶ l) (θ : traversal l.len) :
  apply_map (α ≫ β) θ = apply_map α (apply_map β θ) :=
begin
  induction θ, refl, induction θ_hd with i, induction θ_hd_snd,
  all_goals
  { unfold apply_map, rw [apply_map_append, ←θ_ih],
    apply (list.append_left_inj (apply_map (α ≫ β) θ_tl)).mpr,
    clear θ_ih θ_tl },
  { apply eq_of_sorted_of_same_elem _ _,
    apply apply_map_to_plus_sorted,
    apply apply_map_preserves_sorted,
    apply apply_map_to_plus_sorted,
    intro e, cases e with j, cases e_snd,
    { rw plus_in_apply_map_iff,
      rw [plus_in_apply_map_to_plus_iff, plus_in_apply_map_to_plus_iff],
      simp },
    { rw min_in_apply_map_iff,
      split; intro h; exfalso;
      exact min_notin_apply_map_to_plus _ _ _ _ _ h }},
  { apply eq_of_sorted_of_same_elem _ _,
    apply apply_map_to_min_sorted,
    apply apply_map_preserves_sorted,
    apply apply_map_to_min_sorted,
    intro e, cases e with j, cases e_snd,
    { rw plus_in_apply_map_iff,
      split; intro h; exfalso;
      exact plus_notin_apply_map_to_min _ _ _ _ _ h },
    { rw min_in_apply_map_iff,
      rw [min_in_apply_map_to_min_iff, min_in_apply_map_to_min_iff],
      simp }}
end

def 𝕋₀ : sSet :=
{ obj       := λ n, traversal n.unop.len,
  map       := λ x y α, traversal.apply_map α.unop,
  map_id'   := λ n, traversal.map_id,
  map_comp' := λ l n m β α, funext (λ θ, traversal.comp_apply α.unop β.unop θ) }

def 𝕋₁ : sSet :=
{ obj       := λ x, pointed_traversal x.unop.len,
  map       := λ _ _ α θ, ⟨𝕋₀.map α θ.1, 𝕋₀.map α θ.2⟩,
  map_id'   := λ _, by ext1 θ; simp,
  map_comp' := λ _ _ _ _ _, by ext1 θ; simp }

def cod : 𝕋₁ ⟶ 𝕋₀ :=
{ app         := λ x θ, list.append θ.1 θ.2,
  naturality' := λ x y α, funext (λ θ, (traversal.apply_map_append α.unop θ.1 θ.2).symm) }

def dom : 𝕋₁ ⟶ 𝕋₀ :=
{ app         := λ n θ, θ.2,
  naturality' := λ x y α, by simp; refl }

def as_hom {n} (θ : traversal n) : Δ[n] ⟶ 𝕋₀ := simplex_as_hom θ

def add_point {n} : Π (θ : traversal n), fin(θ.length + 1) → pointed_traversal n
| ⟦⟧       j := ⟨⟦⟧, ⟦⟧⟩
| (h :: t) j := if j.val = 0 then ⟨⟦⟧, h :: t⟩
                else ⟨(add_point t (j-1)).1 ++ ⟦h⟧, (add_point t (j-1)).2⟩

end traversal

def pointed_traversal.as_hom {n} (θ : pointed_traversal n) : Δ[n] ⟶ traversal.𝕋₁ := simplex_as_hom θ

namespace traversal

-- Geometric realisation of a traversal
namespace geometric_realization

variables {n : ℕ} (θ : traversal n)

def s {n} : fin (n+1) × ± → fin (n+2)
| ⟨k, ∔⟩ := k.succ
| ⟨k, ∸⟩ := k.cast_succ

def t {n} : fin (n+1) × ± → fin (n+2)
| ⟨k, ∔⟩ := k.cast_succ
| ⟨k, ∸⟩ := k.succ

@[reducible]
def shape := fin(θ.length + 1) ⊕ fin(θ.length)

namespace shape

inductive hom :  shape θ → shape θ → Type*
| id (X)                 : hom X X
| s  (i : fin(θ.length)) : hom (sum.inl i.cast_succ) (sum.inr i)
| t  (i : fin(θ.length)) : hom (sum.inl i.succ)      (sum.inr i)

instance category : small_category (shape θ) :=
{ hom := hom θ,
  id := λ j, hom.id j,
  comp := λ j₁ j₂ j₃ f g,
  begin
    cases f, exact g,
    cases g, exact hom.s f_1,
    cases g, exact hom.t f_1,
  end,
  id_comp' := λ j₁ j₂ f, rfl,
  comp_id' := λ j₁ j₂ f, by cases f; refl,
  assoc'   := λ j₁ j₂ j₃ j₄ f g h,
  begin
    cases f, refl,
    cases g, refl,
    cases g, refl,
  end
}

end shape

def diagram : shape θ ⥤ sSet :=
{ obj := λ j, sum.cases_on j (λ j, Δ[n]) (λ j, Δ[n+1]),
  map := λ X Y f,
  begin
    cases X; cases Y; cases f,
    exact 𝟙 _,
    exact to_sSet_hom (δ (s (list.nth_le θ Y.1 Y.2))),
    exact to_sSet_hom (δ (t (list.nth_le θ Y.1 Y.2))),
    exact 𝟙 _,
  end,
  map_id'   := λ X, by cases X; refl,
  map_comp' := λ X Y Z f g, by cases X; cases Y; cases Z; cases f; cases g; refl, }

-- @[simp]
-- lemma diagram_map_s {j} : (diagram θ).map (shape.hom.s j) = _ := sorry

def colimit : colimit_cocone (diagram θ) :=
{ cocone := combine_cocones (diagram θ) (λ n,
  { cocone := types.colimit_cocone _,
    is_colimit := types.colimit_cocone_is_colimit _ }),
  is_colimit := combined_is_colimit _ _,
}

end geometric_realization

def geometric_realization {n} (θ : traversal n) : sSet := (geometric_realization.colimit θ).cocone.X

namespace geometric_realization

variables {n : ℕ} (θ : traversal n)

def j_cocone : limits.cocone (diagram θ) :=
{ X := Δ[n],
  ι :=
  { app := λ j,
    begin
      cases j,
      exact 𝟙 _,
      exact to_sSet_hom (σ (list.nth_le θ j.1 j.2).1),
    end,
    naturality' := λ j₁ j₂ f,
    begin
      cases j₁; cases j₂; cases f,
      refl, swap 3, refl,
      change standard_simplex.map (δ (s (list.nth_le θ j₂ _))) ≫ standard_simplex.map (σ (list.nth_le θ j₂ _).fst) = 𝟙 _,
      swap,
      change standard_simplex.map (δ (t (list.nth_le θ j₂ _))) ≫ standard_simplex.map (σ (list.nth_le θ j₂ _).fst) = 𝟙 _,
      all_goals { cases list.nth_le θ _ _, cases snd, },
      all_goals
      { rw [←standard_simplex.map_comp, ←standard_simplex.map_id],
        apply congr_arg, },
      exact δ_comp_σ_self,
      exact δ_comp_σ_succ,
      exact δ_comp_σ_succ,
      exact δ_comp_σ_self,
    end }
}

def j : geometric_realization θ ⟶ Δ[n] :=
  (colimit θ).is_colimit.desc (j_cocone θ)

def k_cocone : cocone (diagram θ) :=
{ X := 𝕋₁,
  ι :=
  { app := λ j,
    begin
      cases j,
      exact (θ.add_point j).as_hom,
      --Special position
      exact (𝕋₁.map (σ (list.nth_le θ j.cast_succ.1 j.2).1).op (θ.add_point j.cast_succ)).as_hom,
    end,
    naturality' := λ j₁ j₂ f,
    begin
      cases j₁; cases j₂; cases f; simp,
      refl, swap 3, refl,
      { ext1, ext1, simp,
        sorry
      },
      { ext1,
        sorry
      },
    end }
}

def k : geometric_realization θ ⟶ 𝕋₁ := (colimit θ).is_colimit.desc (k_cocone θ)

def pullback_cone {n} (θ : traversal n) : pullback_cone (θ.as_hom) cod := pullback_cone.mk (j θ) (k θ)
begin
  sorry
end

-- is_limit_aux
lemma Theorem_9_11 : is_limit (pullback_cone θ) :=
{ lift  := sorry,
  fac'  := sorry,
  uniq' := sorry }


end geometric_realization

end traversal
