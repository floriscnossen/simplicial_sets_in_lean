import algebraic_topology.simplicial_set

open category_theory
open simplex_category
open sSet
open_locale simplicial

inductive pm
| plus  : pm
| minus : pm

local notation `±` := pm
local notation `∔` := pm.plus
local notation `∸` := pm.minus

-- @[reducible]
-- def traversal' (n : ℕ) := list (fin (n+1) × ±)

-- def len {n} : traversal' n → ℕ
-- | list.nil        := 0
-- | (list.cons h t) := 1 + len t

def traversal (n : ℕ) := Σ (l : ℕ), fin l → fin (n+1) × ±

def len {n} : traversal n → ℕ := λ θ, θ.1

@[reducible]
def position {n} (θ : traversal n) := fin (θ.1 + 1)

namespace traversal

-- def len {n} : traversal n → ℕ
-- | list.nil        := 0
-- | (list.cons h t) := 1 + len t

end traversal

def pointed_traversal (n : ℕ) := Σ (θ : traversal n), position θ

def 𝕋₀ : sSet :=
{ obj := λ n, traversal n.unop.len,
  map := sorry,}

def 𝕋₁ : sSet :=
{ obj := λ n, pointed_traversal n.unop.len,
  map := sorry,}

def cod : 𝕋₁ ⟶ 𝕋₀ :=
{ app := λ n ⟨θ, i⟩, θ,
  naturality' := sorry }

def dom : 𝕋₁ ⟶ 𝕋₀ := sorry

def s {n} : fin (n+1) × ± → fin (n+2)
| ⟨k, ∔⟩ := k.succ
| ⟨k, ∸⟩ := k.cast_succ

def t {n} : fin (n+1) × ± → fin (n+2)
| ⟨k, ∔⟩ := k.cast_succ
| ⟨k, ∸⟩ := k.succ
