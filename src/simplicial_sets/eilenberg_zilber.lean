-- import algebraic_topology.simplex_category
import algebraic_topology.simplicial_set
import degeneracy_face

open category_theory
open simplex_category
open_locale simplicial

def degenerate {X : sSet} {n} (x : X _[n]) : Prop :=
∃ {m} {s : [n] ⟶ [m]} [degeneracy s] (y : X _[m]),  m < n ∧ x = (X.map s.op) y

def decomp (X : sSet) {n} (x : X _[n]) (m : ℕ) : Prop :=
∃ {s : [n] ⟶ [m]} [degeneracy s] (y : X _[m]), x = (X.map s.op) y

noncomputable
instance decidable_decomp (X : sSet) {n} (x : X _[n]) : decidable_pred (decomp X x) :=
λ m, classical.dec (decomp X x m)
-- begin
--   intro m,
--   by_cases hnm : m ≤ n, swap,
--   apply decidable.is_false,
--   dsimp[decomp],
--   rintros ⟨s, hs, hy⟩,
--   exact hnm (le_of_degeneracy s hs),

--   exact classical.dec (decomp X x m), --TODO
-- end

lemma eilenberg_zilber (X : sSet) {n} (x : X _[n]) :
  ∃ {m} {s : [n] ⟶ [m]} [degeneracy s] (y : X _[m]), ¬degenerate y ∧ x = (X.map s.op) y :=
begin
  let p := decomp X x,
  have H : ∃ m, p m, refine ⟨n, 𝟙 [n], degeneracy.id, x, _⟩,
  { rw [op_id, X.map_id],
    exact eq.refl x, },
  rcases nat.find_x H with ⟨m, ⟨s, hs, y, hy⟩, hm⟩,
  clear H,
  refine ⟨m, s, hs, y, ⟨_, hy⟩⟩,
  rintro ⟨m', s', hs', y', ⟨hm', hy'⟩⟩,
  apply hm m' hm',
  refine ⟨s ≫ s', degeneracy_comp_degeneracy hs' hs, y', _⟩,
  rw [op_comp, X.map_comp, types_comp_apply, ←hy', ←hy],
end

namespace eilenberg_zilber

lemma same_sections (X : sSet) {n} (x : X _[n]) {m}
{s₁ s₂ : [n] ⟶ [m]} [hs₁ : degeneracy s₁] [hs₂ : degeneracy s₂] (y₁ y₂ : X _[m])
(hy₁ : ¬degenerate y₁) (hy₂ : ¬degenerate y₂) (hy₁y₂ : (X.map s₁.op) y₁ = (X.map s₂.op) y₂)
(f : [m] ⟶ [n]) : f ≫ s₁ = 𝟙 [m] → f ≫ s₂ = 𝟙 [m] :=
begin
  intro hf,
  let u := f ≫ s₂, change u = 𝟙 [m],
  have hu : (X.map u.op) y₂ = y₁,
  { rw [op_comp, X.map_comp, types_comp_apply, ←hy₁y₂],
    rw [←types_comp_apply (X.map s₁.op) (X.map f.op)],
    rw [←X.map_comp, ←op_comp,hf, op_id, X.map_id, types_id_apply], },
  rcases decomp_degeneracy_face u with ⟨k, s₃, hs₃, i₃, hi₃, hs₃i₃⟩,
  have h : ¬k < m,
  { rw [hs₃i₃, op_comp, X.map_comp, types_comp_apply] at hu,
    intro h, apply hy₁,
    unfold degenerate,
    exact ⟨k, s₃, hs₃, X.map i₃.op y₂, ⟨h, hu.symm⟩⟩, },
  push_neg at h,
  have h' : k = m, from (le_antisymm h (le_of_degeneracy s₃ hs₃)).symm,
  rw hs₃i₃,
  exact @id_of_auto _ _ (@is_iso.comp_is_iso _ _ _ _ _ _ _
    (iso_of_degeneracy_auto s₃ hs₃ h') (iso_of_face_auto i₃ hi₃ h')),
end

lemma unique (X : sSet) {n} (x : X _[n]) {m}
{s₁ s₂ : [n] ⟶ [m]} [hs₁ : degeneracy s₁] [hs₂ : degeneracy s₂] (y₁ y₂ : X _[m])
(hy₁ : ¬degenerate y₁) (hy₂ : ¬degenerate y₂) (hy₁y₂ : (X.map s₁.op) y₁ = (X.map s₂.op) y₂) :
  s₁ = s₂ ∧ y₁ = y₂ :=
begin
  split,
  { apply eq_of_same_sections,
    intro f, split,
    exact same_sections X x y₁ y₂ hy₁ hy₂ hy₁y₂ f,
    exact same_sections X x y₂ y₁ hy₂ hy₁ hy₁y₂.symm f },
  { cases split_epi_of_degeneracy hs₁ with f hf,
    simp only [auto_param_eq] at *,
    have hu : f ≫ s₂ = 𝟙 [m], from same_sections X x y₁ y₂ hy₁ hy₂ hy₁y₂ f hf,
    let u := f ≫ s₂, change u = 𝟙 [m] at hu,
    have hu' : (X.map u.op) y₂ = y₁,
    { rw [op_comp, X.map_comp, types_comp_apply, ←hy₁y₂],
      rw [←types_comp_apply (X.map s₁.op) (X.map f.op)],
      rw [←X.map_comp, ←op_comp,hf, op_id, X.map_id, types_id_apply], },
    rw [hu, op_id, X.map_id,types_id_apply] at hu',
    exact hu'.symm }
end

end eilenberg_zilber
