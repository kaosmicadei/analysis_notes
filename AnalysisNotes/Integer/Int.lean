import AnalysisNotes.Natural


def ℤ₀ : Type := ℕ×ℕ

namespace ℤ₀

@[simp] def eq (x y : ℤ₀) : Prop := x.1 + y.2 = x.2 + y.1

theorem eq_refl (x : ℤ₀) : eq x x := by simp
theorem eq_symm {x y : ℤ₀} (h : eq x y) : eq y x := by simp at *; rw [h]
theorem eq_trans {x y z : ℤ₀} (h₁ : eq x y) (h₂ : eq y z) : eq x z := by
  simp at *
  apply ℕ.add_cancel_right _ _ y.1
  -- LHS
  rw [ℕ.add_assoc, ℕ.add_comm z.2, h₂, ← ℕ.add_assoc, ℕ.add_comm x.1]
  -- RHS
  rw [ℕ.add_assoc z.1 x.2, ℕ.add_comm x.2, ← h₁, ← ℕ.add_assoc]

instance eq.eqv : Equivalence eq where
  refl := eq_refl
  symm := eq_symm
  trans := eq_trans

example (x : ℤ₀) : x = x := rfl

instance intSetiod : Setoid ℤ₀ where
  r := eq
  iseqv := eq.eqv

end ℤ₀


def ℤ : Type := Quotient ℤ₀.intSetiod

namespace ℤ

def mk (n : ℤ₀) : ℤ := Quotient.mk _ n

instance (n : Nat) : OfNat ℤ n where
  ofNat := mk (ℕ.fromNat n, 0)

@[simp] def neg' : ℤ₀ → ℤ := λ (a, b) => mk (b , a)

theorem neg_well_defined (x y : ℤ₀) (h : x ≈ y) : neg' x = neg' y := by
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r] at *
  rw [h]

instance : Neg ℤ where
  neg := Quotient.lift neg' neg_well_defined

#check (1 : ℤ)
#check (-1 : ℤ)

@[simp] def add' : ℤ₀ → ℤ₀ → ℤ := λ (a, b) (c, d) => mk (a + c, b + d)

theorem add_well_defined (a b c d : ℤ₀) (h₁ : a ≈ c) (h₂ : b ≈ d) :
  add' a b = add' c d
  := by
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r] at *
  -- LHS
  rw [← ℕ.add_assoc b.1, ℕ.add_comm b.1, ℕ.add_assoc c.2, ← ℕ.add_assoc a.1, h₁, h₂, ← ℕ.add_assoc]
  -- RHS
  rw [← ℕ.add_assoc d.1, ← ℕ.add_assoc, ℕ.add_comm d.1, ← ℕ.add_assoc]

@[simp] def add : ℤ → ℤ → ℤ := Quotient.lift₂ add' add_well_defined

instance : Add ℤ where
  add := add

#check (1 : ℤ) + 1
#check (1 : ℤ) + (-1)

instance : Sub ℤ where
  sub := λ a b => a + (-b)

#check (1 : ℤ) - 1

@[simp]
theorem add_inv_eq_zero (n : ℤ) : n + (-n) = 0 := by
  cases n using Quotient.ind
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r, ℕ.zero_eq_nat_zero]

theorem add_zero (n : ℤ) : n + 0 = n := by
  cases n using Quotient.ind
  simp [add]
  sorry

example (a b c d : ℤ) (h : a + c = b + d) : a - b = c - d := by
  sorry

end ℤ
