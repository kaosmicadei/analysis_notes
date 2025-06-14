import AnalysisNotes.Natural


structure ℤ where
  mk :: (a b : ℕ)
  deriving Repr


namespace ℤ

def fromNat : Nat → ℤ
  | 0 => ⟨0, 0⟩
  | n => ⟨ℕ.fromNat n, 0⟩

instance (n : Nat) : OfNat ℤ n where
  ofNat := fromNat n

#eval (2 : ℤ)

def toInt : ℤ → Int := λ ⟨a, b⟩ => a.toNat - b.toNat

instance : Repr ℤ where
  reprPrec n _ := repr (toInt n)

#eval ℤ.mk 0 2
#eval ℤ.mk 0 0
#eval ℤ.mk 3 2

@[simp] def neg : ℤ → ℤ := λ ⟨a, b⟩ => ⟨b, a⟩

notation "⁻" x => neg x

#eval ⁻0
#eval ⁻1

@[simp] def eqv : ℤ → ℤ → Prop := λ ⟨a, b⟩ ⟨c, d⟩ => a + d = b + c

notation x " ∼ " y => eqv x y

@[simp] theorem eqv_refl (x : ℤ) : x ∼ x := by simp
@[simp] theorem eqv_symm {x y : ℤ} (h : x ∼ y) : y ∼ x := by simp at *; rw [h]
@[simp] theorem eqv_trans {x y z : ℤ} (h₁ : x ∼ y) (h₂ : y ∼ z) : x ∼ z := by
  simp at *
  apply ℕ.add_cancel_right _ _ y.a
  -- LHS
  rw [ℕ.add_assoc, ℕ.add_comm z.b, h₂, ← ℕ.add_assoc, ℕ.add_comm x.a]
  -- RHS
  rw [ℕ.add_assoc z.a x.b, ℕ.add_comm x.b, ← h₁, ← ℕ.add_assoc]

instance : DecidableRel eqv :=
  λ ⟨a, b⟩ ⟨c, d⟩ => inferInstanceAs (Decidable (a + d = b + c))

#eval 0 ∼ ⁻0
#eval (1 ∼ ⁻1) -> False

@[simp] def add : ℤ → ℤ → ℤ := λ ⟨a, b⟩ ⟨c, d⟩ => ⟨a + c, b + d⟩

instance : Add ℤ where
  add := add

#eval (2 : ℤ) + 3
#eval (2 : ℤ) + ⁻3

@[simp] def sub (x y : ℤ) : ℤ := x + ⁻y

instance : Sub ℤ where
  sub := sub

#eval ((1 : ℤ) - 1) ∼ 0

@[simp] def mul : ℤ → ℤ → ℤ := λ ⟨a, b⟩ ⟨c, d⟩ => ⟨a * d, b * c⟩

instance : Mul ℤ where
  mul := mul

#check (⁻3) * 2
#eval  (⁻3) * 2

instance intSetoid : Setoid ℤ where
  r := eqv
  iseqv := ⟨eqv_refl, eqv_symm, eqv_trans⟩

end ℤ


-- def ℤ₁ := Quotient ℤ.intSetoid
