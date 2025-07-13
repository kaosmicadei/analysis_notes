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
  deriving DecidableEq


namespace ℕ

-- Notation & Conveniences
-- =======================

-- Define `x⁺` as shorthand for `succ x` to improve clarity in later theorems.
notation x "⁺" => succ x

-- Parsing Digits as ℕ
-- -------------------

-- We declare ℕ as a countable type (`OfNat`) in order to type, e.g., `2`
-- instead of `ℕ.succ (ℕ.succ ℕ.zero)`. We do that in two steps.

-- First, we define a map between a digit (Lean's built-in definition of
-- Natural Numbers).
@[simp]
def fromNat : Nat → ℕ
  | 0 => zero
  | Nat.succ n => ℕ.succ (fromNat n)

-- Than we instantiate ℕ as `countable`.
instance (n : Nat) : OfNat ℕ n where
  ofNat := fromNat n

-- Validation checks.
#eval (0 : ℕ)
#eval (1 : ℕ)
#eval (2 : ℕ)
-- it also allows comparisons
#eval 1 = 0⁺
#eval 2 = ℕ.succ (ℕ.succ ℕ.zero)

-- Representing ℕ as Dgits
-- -----------------------

-- The same way we can conveniently parse digits to ℕ, we can pretty-print ℕ to
-- digits.

-- First, we define "reverse" map so Lean can construct built-in naturals from
-- ℕ.
@[simp]
def toNat : ℕ → Nat
  | zero => 0
  | succ n => 1 + toNat n

-- Then, we instantiate the representation of ℕ as the represetation of its
-- `Nat` counterpart.
instance : Repr ℕ where
  reprPrec n _ := repr (toNat n)

-- Validation check.
#eval ℕ.succ (ℕ.succ ℕ.zero)  -- 2


-- Simplification Support for ` simp` Tools
-- ========================================

-- Lean's simplification tools (`simp`) require theorems (not just definitions)
-- to perform rewrites. The following theorems enable automated rewriting of
-- common expressions.

-- Rewriting tools doesn't coerce types automatically. In this case, 0 and 1
-- will not automatically replace by ℕ.zero and (ℕ.succ ℕ.zero) repesctively.
-- However, it's very convenient to using 0 and 1 when defining theorems to keep
-- them visually simple. For that, we add some trival theorems. These theorems
-- are not automatically `simp` since they can led to no terminated recusrion.
theorem nat_zero_eq_zero : 0 = ℕ.zero := rfl
theorem zero_eq_nat_zero : ℕ.zero = 0 := rfl
theorem nat_one_eq_zero : 1 = ℕ.succ ℕ.zero := rfl
theorem one_eq_nat_zero : ℕ.succ ℕ.zero = 1 := rfl

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

-- Equality Transitivity
-- =====================

theorem eq_trans(a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁]
  exact h₂

end ℕ
