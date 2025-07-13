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

end ℤ
