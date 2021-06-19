import algebraic_topology.simplicial_set

open category_theory
open category_theory.limits
open simplex_category
open sSet
open_locale simplicial

/-! # Simplex as hom
Defines the functions simplex as hom. This is the function that turns a simplex into a morphism
from a standard simplex to the simplicial set.
-/


namespace simplex_category

@[simps] def last (n : simplex_category) := fin.last n.len

def op (n : simplex_category) := opposite.op n

end simplex_category

namespace sSet

/-- Interpret a simplex as a morphism from a standard simplicial set. -/
def simplex_as_hom {n} {X : sSet} (x : X.obj (opposite.op n)) :
  standard_simplex.obj n ⟶ X :=
{ app := λ m f,
  begin
    change m.unop ⟶ n at f,
    exact X.map f.op x,
  end,
  naturality' := λ k m f,
  begin
    ext1 g, change k.unop ⟶ n at g, simp,
    rw [←types_comp_apply (X.map g.op) (X.map f), ←X.map_comp],
    refl,
  end
}

lemma simplex_as_hom_id {n} {X : sSet} (x : X.obj (opposite.op n)) :
  (simplex_as_hom x).app (opposite.op n) (𝟙 n) = x :=
begin
  change X.map (𝟙 n).op x = x,
  rw [op_id, X.map_id],
  refl,
end

lemma simplex_as_hom_eq_iff {n} {X : sSet} (x y : X.obj (opposite.op n)) :
  simplex_as_hom x = simplex_as_hom y ↔ x = y :=
begin
  split,
  { intro h, rwa [←simplex_as_hom_id x, ←simplex_as_hom_id y, h] },
  { intro h, rwa h }
end

/-- Interpret a morphism in the simplex category as a morphism between standard simplicial sets. -/
def to_sSet_hom {n m} (f : [n] ⟶ [m]) : Δ[n] ⟶ Δ[m] := sSet.standard_simplex.map f

@[simp]
lemma to_sSet_hom_id {n} : to_sSet_hom (𝟙 [n]) = 𝟙 Δ[n] := yoneda.map_id [n]

lemma hom_comp_simplex_as_hom {n m} (f : [n] ⟶ [m]) {X : sSet} (x : X.obj (opposite.op [m])) :
  to_sSet_hom f ≫ simplex_as_hom x = simplex_as_hom (X.map f.op x) :=
begin
  ext k g, change k.unop ⟶ [n] at g,
  simp [to_sSet_hom, simplex_as_hom],
  rw [←types_comp_apply (X.map f.op) (X.map g.op) x, ←X.map_comp],
  refl,
end

lemma simplex_as_hom_comp_hom {n} {X Y : sSet} (x : X.obj (opposite.op n)) (f : X ⟶ Y) :
  simplex_as_hom x ≫ f = simplex_as_hom (f.app (opposite.op n) x) :=
begin
  ext k g, change k.unop ⟶ n at g,
  simp [to_sSet_hom, simplex_as_hom],
  rw [←types_comp_apply (X.map g.op) (f.app k) x, ←types_comp_apply (f.app _) (Y.map g.op) x],
  apply congr_fun,
  apply f.naturality,
end

end sSet
