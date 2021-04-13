import algebraic_topology.simplicial_set

open category_theory
open simplex_category
open sSet
open_locale simplicial

open category_theory.limits

def to_sSet_hom {n m} (f : [n] ⟶ [m]) : Δ[n] ⟶ Δ[m] := sSet.standard_simplex.map f

noncomputable
def pullback_σ {n} (i : fin (n+1)) := limits.pullback (to_sSet_hom (σ i)) (to_sSet_hom (σ i))

noncomputable
def σ_succ_σ {n} (i : fin (n+1)) : Δ[n+2] ⟶ pullback_σ i :=
  pullback.lift (to_sSet_hom (σ i.succ)) (to_sSet_hom (σ i.cast_succ))
begin
  dsimp [to_sSet_hom],
  rw [←standard_simplex.map_comp', ←standard_simplex.map_comp'],
  apply congr_arg,
  exact (@σ_comp_σ n i i (le_refl i)).symm,
end

noncomputable
def σ_σ_succ {n} (i : fin (n+1)) : Δ[n+2] ⟶ pullback_σ i :=
  pullback.lift (to_sSet_hom (σ i.cast_succ)) (to_sSet_hom (σ i.succ))
begin
  dsimp [to_sSet_hom],
  rw [←standard_simplex.map_comp', ←standard_simplex.map_comp'],
  apply congr_arg,
  exact @σ_comp_σ n i i (le_refl i),
end

noncomputable
def pushout_cocone_δ_succ {n} (i : fin (n+1)) :
  pushout_cocone (to_sSet_hom (δ i.succ.cast_succ)) (to_sSet_hom (δ i.succ.cast_succ)) :=
begin
  apply pushout_cocone.mk (σ_succ_σ i) (σ_σ_succ i),
  unfold σ_succ_σ σ_σ_succ to_sSet_hom,
  ext1,
  all_goals
  { simp,
    rw [←standard_simplex.map_comp', ←standard_simplex.map_comp'],
    apply congr_arg,
    rw [δ_comp_σ_self, fin.cast_succ_fin_succ, δ_comp_σ_succ], },
end

noncomputable
lemma pullback_σ_is_pushout_δ_succ {n} {i : fin (n+1)} : is_colimit (pushout_cocone_δ_succ i) :=
begin
  apply pushout_cocone.is_colimit_aux,
  sorry,
  sorry,
  sorry,
  sorry
end
