/-
  Peano's Natural Numbers
  =======================

  This file redefines natural numbers using Peano's axioms for didactic clarity.
  It introduces natural number construction, basic notations, and key theorems
  about their behavior.
-/

-- Peano's axioms (definition of natural numbers).
inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ
  deriving Repr, DecidableEq


namespace ℕ

-- Notation & Conveniences
-- =======================

-- Define `x⁺` as shorthand for `succ x` to improve clarity in later theorems.
notation x "⁺" => succ x

-- This instance allows `0` to be used as notation for `zero`.
instance : Zero ℕ where
  zero := ℕ.zero

-- This instance allows to use 1 as instead of `succ zero` or even `0⁺`.
instance : One ℕ where
  one := succ zero

-- Basic checks.
#check (0 : ℕ)
#check (1 : ℕ)
#eval 1 == 0⁺


-- Simplification Support for ` simp` Tools
-- ========================================

-- Lean's simplification tools (`simp`) require theorems (not just definitions)
-- to perform rewrites. The following theorems enable automated rewriting of
-- common expressions.

-- Allows `simp` to recognise the equivalence of `1` and `succ zero`.
@[simp]
theorem one_eq_succ_zero : 1 = 0⁺ := rfl

-- Zero is not a Sucessor
-- ===============================

-- A core idea on Peano's construction is that natural numbers have a base
-- element (zero) which is not the successor of any number. Here we prove it by
-- showing that constructing an equality `0 = n⁺` fails structurally.

@[simp]
theorem zero_not_succ (n : ℕ) : 0 = n⁺ → False :=
  λ h => nomatch h


-- Successor Injectitivy
-- =====================

-- The injectivity of the successor function can be shown in two directions.
-- Forward direction (modus ponens): if `a⁺ = b⁺` then `a = b`.
example (a b : ℕ) : a⁺ = b⁺ → a = b
  | Eq.refl _ => rfl

-- Backward direction (modus ponens reverse): if `a = b` then `a⁺ = b⁺`.
example (a b : ℕ) : a = b → a⁺ = b⁺ :=
  λ h => by rw [h]

-- In Lean, both directions can be combined into a bi-implication using `↔`.
@[simp]
theorem succ_inj {a b : ℕ} : a⁺ = b⁺ ↔ a = b :=
  Iff.intro
    (λ hypotesis =>
      match hypotesis with
      | Eq.refl _ => rfl)
    (λ hypotesis => by rw [hypotesis])


-- Usage Examples of Successor Injectivity
-- =======================================

section
  variable (a b : ℕ)
  variable (h₁ : a⁺ = b⁺) (h₂ : a = b)

  -- Both forms are equivalent. The first looks easier in tactic mode.
  #check Iff.mp  succ_inj h₁
  #check Iff.mpr succ_inj h₂

  -- This form seems more concise for coding in general.
  #check succ_inj.mp  h₁
  #check succ_inj.mpr h₂
end

theorem eq_trans(a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁]
  exact h₂

end ℕ


-- section

-- variable {α : Type} (P : α → Prop) (Q : Prop)

-- example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
--   intro x
--   rcases h with x
--   rcases h with x
--   apply False.elim

--   sorry

-- example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
--   sorry

-- example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
--   sorry

-- example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
--   sorry

-- end
