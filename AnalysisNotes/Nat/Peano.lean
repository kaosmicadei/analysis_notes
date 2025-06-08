-- Peano's natural numbers definition.
-- ⚠️ This shadowing of ℕ is intentional. This is our custom Peano ℕ.
inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ
  deriving Repr, DecidableEq


namespace ℕ

instance : Zero ℕ where
  zero := ℕ.zero

instance : One ℕ where
  one := succ zero

#check (0 : ℕ)
#check (1 : ℕ)

notation x "⁺" => succ x
#eval 1 == 0⁺

@[simp]
theorem one_eq_succ_zero : 1 = 0⁺ := rfl

-- Prove successor is an injective function.
section
-- Successor is an injective (modus ponens)
theorem succ_inj_mp (a b : ℕ) : a⁺ = b⁺ → a = b
  | Eq.refl _ => rfl

-- Successor is an injective (modus ponens reverse)
theorem succ_inj_mpr (a b : ℕ) : a = b → a⁺ = b⁺ :=
  λ h => by rw [h]
end

@[simp]
theorem succ_inj (a b : ℕ) : a⁺ = b⁺ ↔ a = b :=
  Iff.intro
    (λ h =>
      match h with
      | Eq.refl _ => rfl)
    (λ h => by rw [h])

end ℕ
