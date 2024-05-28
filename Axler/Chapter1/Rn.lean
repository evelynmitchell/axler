import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic


/-- A structure that's a cumbersome way of writing `n: ℕ → Fin n → ℝ` -/
@[ext]
structure Rn (n: ℕ) where
  /-- The vector in `ℝ^n`-/
  term: Fin n → ℝ

instance addRn: Add (Rn n) where
  add a b := ⟨fun n => a.term n + b.term n⟩

@[simp]
theorem term_add_apply {n: ℕ} {a b : (Rn n)} {x: Fin n}: (a + b).term x = a.term x + b.term x := rfl

instance zeroRn: Zero (Rn n) where
  zero := ⟨fun _ => 0⟩

@[simp]
theorem zero_term: (0 :Rn n).term x = 0 := rfl

instance negRn: Neg (Rn n) where
  neg r := ⟨fun n => -(r.term n)⟩

@[simp]
theorem neg_term {a: Rn n}: (-a).term = -(a.term) := rfl

instance addCommGroupRn: AddCommGroup (Rn n) where
  add_comm a b := by  ext ; simp [add_comm]
  add_assoc a b c := by ext ; simp [add_assoc]
  zero := zeroRn.zero
  add_zero a := by ext ; simp
  zero_add a := by ext ; simp
  add_left_neg a := by ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec


instance smulRn: SMul ℝ (Rn n) where
  smul x a := ⟨fun n => x * a.term n⟩

@[simp]
theorem term_smul_apply {x: ℝ} {a : Rn n} {y: Fin n}: (x • a).term y = x • (a.term y) := rfl


instance moduleRn: Module ℝ (Rn n) where
  one_smul a := by ext; simp
  zero_smul a := by ext x; simp only [term_smul_apply, smul_eq_mul, zero_mul, zero_term]
  smul_zero a := by ext; simp
  smul_add a b c := by ext; simp [mul_add]
  add_smul a b c := by ext; simp [add_mul]
  mul_smul a b c := by ext; simp [mul_assoc]
