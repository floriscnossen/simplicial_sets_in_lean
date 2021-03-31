import algebraic_topology.simplex_category
import algebraic_topology.simplicial_set
import degeneracy
import face

open category_theory
open simplex_category
open_locale simplicial

def op (n : simplex_category) : simplex_categoryᵒᵖ := opposite.op n

def degenerate {X : sSet} {n} (x : X.obj (op [n])) : Prop :=
  ∃ {m} {s : [n] ⟶ [m]} [degeneracy s] (y : X.obj (op [m])),
  m < n ∧ x = (X.map s.op) y



lemma eilenberg_zilber (X : sSet) {n} (x : X.obj (op [n])) :
  ∃ {m} {s : [n] ⟶ [m]} [degeneracy s] (y : X.obj (op [m])),
  ¬ degenerate y ∧ x = (X.map s.op) y :=
begin
  let p : ℕ → Prop := λ m, ∃ {s : [n] ⟶ [m]} [degeneracy s] (y : X.obj (op [m])), x = (X.map s.op) y,
  let dp : decidable_pred p := sorry,
  have H : ∃ m, p m, refine ⟨n, 𝟙 [n], degeneracy.id, x, _⟩,
  { rw [op_id, X.map_id],
    exact eq.refl x, },
  rcases @nat.find_x p dp H with ⟨m, ⟨s, hs, y, hy⟩, hm⟩,
  clear H,
  refine ⟨m, s, hs, y, ⟨_, hy⟩⟩,
  rintro ⟨m', s', hs', y', ⟨hm', hy'⟩⟩,
  apply hm m' hm',
  refine ⟨s ≫ s', degeneracy_comp_degeneracy hs' hs, y', _⟩,
  rw [op_comp, X.map_comp, types_comp_apply, ←hy', ←hy],
end

lemma eilenberg_zilber_unique (X : sSet) {n} (x : X.obj (op [n])) {m}
{s₁ s₂ : [n] ⟶ [m]} [degeneracy s₁] [degeneracy s₂] (y₁ y₂ : X.obj (op [m])) :
  ¬ degenerate y₁ → ¬ degenerate y₂ → ((X.map s₁.op) y₁ = (X.map s₂.op) y₂) →
  s₁ = s₂ ∧ y₁ = y₂ :=
begin
  sorry
end
