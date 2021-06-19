import traversals.basic

open category_theory
open category_theory.limits
open simplex_category
open sSet
open_locale simplicial

/-! # Geometric realisation of a traversal -/

namespace traversal

namespace geom_real

variables {n : ℕ} (θ : traversal n)

@[reducible]
def shape := fin(θ.length + 1) ⊕ fin(θ.length)

namespace shape

inductive hom : shape θ → shape θ → Type*
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
  assoc'   := λ j₁ j₂ j₃ j₄ f g h,  by cases f; cases g; refl,
}

end shape

def diagram : shape θ ⥤ sSet :=
{ obj := λ j, sum.cases_on j (λ j, Δ[n]) (λ j, Δ[n+1]),
  map := λ _ _ f,
  begin
    cases f with _ j j,
    exact 𝟙 _,
    exact to_sSet_hom (δ (list.nth_le θ j.1 j.2).s),
    exact to_sSet_hom (δ (list.nth_le θ j.1 j.2).t),
  end,
  map_id'   := λ j, rfl,
  map_comp' := λ _ _ _ f g, by cases f; cases g; refl, }

def colimit : colimit_cocone (diagram θ) :=
{ cocone := combine_cocones (diagram θ) (λ n,
  { cocone := types.colimit_cocone _,
    is_colimit := types.colimit_cocone_is_colimit _ }),
  is_colimit := combined_is_colimit _ _,
}

end geom_real

def geom_real {n} (θ : traversal n) : sSet := (geom_real.colimit θ).cocone.X

end traversal
