import Mathlib.Tactic
import Lean
set_option linter.dupNamespace false
namespace Logic
end Logic
open Algebra Lean Elab Tactic Meta Logic Set
notation:max x "²" => x ^ 2  -- square
export Set (Ioo Ico Iio Icc Iic Ioc Ici Ioi)
export Finset (range)

class IntegerRing (Z : Type) extends LinearOrderedSemiring Z, Sub Z, Div Z, Mod Z where
  succ_le_of_lt {a b : Z} : a < b → a + 1 ≤ b
  le_pred_of_lt {a b : Z} : a < b → a ≤ b - 1
  div_add_mod {n d : Z} : n = n / d * d + n % d
  add_sub_cancel (a b : Z) : a + b - b = a

instance : IntegerRing Nat where
  succ_le_of_lt := Nat.succ_le_of_lt
  le_pred_of_lt := Nat.le_pred_of_lt
  div_add_mod {n d : Nat} := by
    rw [Nat.mul_comm]
    apply Eq.symm
    apply Nat.div_add_mod n d
  add_sub_cancel := Nat.add_sub_cancel

instance : IntegerRing Int where
  succ_le_of_lt := Int.add_one_le_of_lt
  le_pred_of_lt := Int.le_sub_one_of_lt
  div_add_mod {n d : Int} := by
    apply Eq.symm
    rw [Int.add_comm]
    rw [Int.mul_comm]
    apply Int.emod_add_ediv
  add_sub_cancel := Int.add_sub_cancel

lemma Algebra.MulAdd.eq.AddMulS
  [Mul α] [Add α] [RightDistribClass α]
  {a b c : α} :
  (a + b) * c = a * c + b * c := by
  rw [right_distrib]

lemma Algebra.NegMul.eq.MulNeg
  [Mul α] [HasDistribNeg α]
  {a b : α} :
  -(a * b) = -a * b := by
  rw [neg_mul_eq_neg_mul]

lemma Algebra.AddMulS.eq.MulAdd
  [Mul α] [Add α] [RightDistribClass α]
  {a b c : α} :
  a * c + b * c = (a + b) * c := by
  rw [MulAdd.eq.AddMulS]

/--
This lemma demonstrates that in a `SubNegMonoid`, subtraction of two elements `a` and `b` is equivalent to adding the additive inverse of `b` to `a`.
Specifically, it states that `a - b = a + -b`, leveraging the algebraic property that subtraction can be defined as addition of the inverse.
This identity is fundamental for simplifying expressions and proving further algebraic properties within structures that support subtraction and negation.
-/
lemma Algebra.Sub.eq.Add_Neg
  [SubNegMonoid α]
  {a b : α} :
  a - b = a + -b := by
  rw [sub_eq_add_neg]

lemma Algebra.MulSub.eq.SubMulS.nat
  {x a b : ℕ} :
  (a - b) * x = a * x - b * x := by
  rw [Nat.sub_mul]

lemma Algebra.MulSub.eq.SubMulS
  [Ring α]
  {x a b : α} :
  (a - b) * x = a * x - b * x := by
  rw [Sub.eq.Add_Neg (a := a)]
  rw [← AddMulS.eq.MulAdd]
  rw [Sub.eq.Add_Neg]
  rw [NegMul.eq.MulNeg]

lemma Algebra.SubMulS.eq.MulSub.nat
  {x a b : ℕ} :
  a * x - b * x = (a - b) * x := by
  rw [MulSub.eq.SubMulS.nat]

lemma Algebra.SubMulS.eq.MulSub
  [Ring α]
  {x a b : α} :
  a * x - b * x = (a - b) * x := by
  rw [MulSub.eq.SubMulS]

/--
This lemma asserts the commutativity of the multiplication operation in a commutative magma.
Specifically, for any elements `a` and `b` in the magma, the product `a * b` is equal to `b * a`, as established by the underlying commutative property of the magma's binary operation.
-/
lemma Algebra.Mul.comm
  [CommMagma α]
  {a b : α} :
  a * b = b * a := by
  apply mul_comm

/--
In a `DivInvMonoid`, division of `a` by `b` is defined as multiplication of `a` by the inverse of `b`.
This lemma confirms the equivalence `a / b = a * b⁻¹`, enabling the use of inverse properties in algebraic expressions involving division.
-/
lemma Algebra.Div.eq.Mul_Inv
  [DivInvMonoid α]
  {a b : α} :
  a / b = a * b⁻¹ := by
  rw [div_eq_mul_inv]

lemma Algebra.Div_Mul.eq.DivDiv
  [DivisionCommMonoid α]
  {a b c : α} :
  a / (b * c) = a / b / c := by
  rw [div_mul_eq_div_div]

lemma Algebra.DivMul.eq.Mul_Div
  [DivInvMonoid α]
  {a b c : α} :
  a * b / c = a * (b / c) := by
  rw [mul_div_assoc]

lemma Algebra.Div_Mul.eq.Inv.of.Ne_0.inv'
  [Field α]
  {a b : α}
  (h : a ≠ 0) :
  a / (a * b) = b⁻¹ := by
  rw [Div_Mul.eq.DivDiv]
  simp [h]

open Algebra.Div_Mul.eq.Inv.of.Ne_0 in
/--
open namespace in
-/
lemma Algebra.Div_Mul.eq.Inv.of.Ne_0
  [Field α]
  {a b : α}
  (h : a ≠ 0)
  (comm : Bool := false) :
  match comm with
  | true =>
    a / (b * a) = b⁻¹
  | false =>
    a / (a * b) = b⁻¹ := by
  cases comm with
  | true =>
    simp
    rw [Mul.comm]
    apply inv' h
  | false =>
    simp
    apply inv' h

/--
This lemma establishes that in a preorder, a strict inequality `x < y` implies the corresponding non-strict inequality `x ≤ y`.
It converts the strict order relation into a non-strict one, leveraging the properties of the preorder structure.
-/
lemma Algebra.Le.of.Lt
  [Preorder α]
  {x y : α}
  (h : x < y) :
  x ≤ y :=
  le_of_lt h

lemma Algebra.SubDivS.eq.DivSub
  [Field α]
  {x y a : α} :
  x / a - y / a = (x - y) / a := by
  rw [Div.eq.Mul_Inv]
  rw [Div.eq.Mul_Inv]
  rw [Div.eq.Mul_Inv]
  rw [SubMulS.eq.MulSub]

lemma Algebra.DivMul.eq.MulDiv
  [DivisionCommMonoid α]
  {a b c : α} :
  a * b / c = a / c * b := by
  rw [mul_div_right_comm]

/--
This lemma confirms that in a monoid, the square of an element `x` is defined as the product of `x` with itself.
It ensures the consistency of exponentiation with the monoid's multiplicative structure, serving as a basic yet essential property in algebraic manipulations.
-/
lemma Algebra.Square.eq.Mul
  [Monoid α]
  {x : α} :
  x² = x * x :=
  pow_two x

/--
This lemma asserts the associativity of the multiplication operation in a semigroup, confirming that the grouping of elements in a product does not affect the result.
Specifically, it states that for any elements `a`, `b`, and `c` in a semigroup, the product `a * b * c` is equal to `a * (b * c)`, leveraging the inherent associative property of the semigroup's binary operation.
-/
lemma Algebra.MulMul.eq.Mul_Mul
  [Semigroup α]
  {a b : α} :
  a * b * c = a * (b * c) := by
  rw [mul_assoc]

/--
This lemma converts a strict order relation `x < y` into a proof that `x` and `y` are distinct.
In a preorder, `x < y` inherently implies `x ≠ y`, and this lemma provides a direct way to extract the inequality from the strict order relation.
-/
lemma Algebra.Ne.of.Lt
  [Preorder α]
  {x y : α}
  (h : x < y) :
  x ≠ y :=
  ne_of_lt h

lemma Algebra.EqMulDiv.of.Ne_0
  [Field α]
  {b : α}
  (h : b ≠ 0)
  (a : α) :
  a / b * b = a := by
  simp [h]

/--
This lemma establishes that the product of an element with itself in a monoid is equal to its square.
It serves as the converse to the axiom `Square.eq.Mul`, enabling the interchange between multiplicative and squared notations.
-/
lemma Algebra.Mul.eq.Square
  [Monoid α]
  {x : α} :
  x * x = x² := by
  rw [Square.eq.Mul]

lemma Algebra.DivDiv.eq.Div_Mul
  [DivisionCommMonoid α]
  {a b c : α} :
  a / b / c = a / (b * c) := by
  rw [Div_Mul.eq.DivDiv]

/--
This lemma confirms the associativity of multiplication in a semigroup by showing that `a * (b * c)` equals `a * b * c`.
It provides the reverse direction of the associativity axiom, enabling flexible rearrangement of multiplicative expressions.
-/
lemma Algebra.Mul_Mul.eq.MulMul
  [Semigroup α]
  {a b : α} :
  a * (b * c) = a * b * c := by
  rw [MulMul.eq.Mul_Mul]

lemma Algebra.Mul_Div.eq.DivMul
  [DivInvMonoid α]
  {a b c : α} :
  a * (b / c) = a * b / c := by
  rw [DivMul.eq.Mul_Div]

lemma Algebra.Eq.of.Le.Ge
  [PartialOrder α]
  {a b : α}
  (h₀ : a ≤ b)
  (h₁ : a ≥ b) :
  a = b :=
  le_antisymm h₀ h₁

lemma Algebra.SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0
  [Field α]
  {a b x y : α}
  (h0 : a ≠ 0)
  (h1 : b ≠ 0) :
  x / a - y / b = (x * b - y * a) / (a * b) := by
  rw [Div.eq.Mul_Inv]
  rw [Div.eq.Mul_Inv]
  rw [← SubDivS.eq.DivSub]
  rw [DivMul.eq.Mul_Div]
  rw [Div_Mul.eq.Inv.of.Ne_0 h1 true]
  rw [DivMul.eq.Mul_Div]
  rw [Div_Mul.eq.Inv.of.Ne_0 h0]

/--
This lemma asserts the commutativity of the addition operation in an additive commutative magma (`AddCommMagma`).
It demonstrates that for any two elements `a` and `b` in the magma, the sum `a + b` is equal to `b + a`, a property inherent to the structure's algebraic definition.
-/
lemma Algebra.Add.comm
  [AddCommMagma α]
  {a b : α} :
  a + b = b + a := by
  apply add_comm

/--
This lemma states that multiplying both sides of an inequality by a non-negative element preserves the inequality.
Specifically, if `x ≥ 0` and `a ≤ b`, then `x * a ≤ x * b`.
This holds in a preordered algebraic structure where multiplication by non-negative elements is monotonic.
-/
lemma Algebra.LeMulS.of.Ge_0.Le
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
  (h1 : x ≥ 0)
  (h2 : a ≤ b) :
  x * a ≤ x * b := by
  exact mul_le_mul_of_nonneg_left h2 h1

lemma Algebra.MulDiv.eq.DivMul
  [DivisionCommMonoid α]
  {a b c : α} :
  a / c * b = a * b / c := by
  rw [DivMul.eq.MulDiv]

lemma Algebra.SubMulS.eq.Mul_Sub.nat
  {x a b : ℕ} :
  x * a - x * b = x * (a - b) := by
  rw [Nat.mul_sub]

/--
This lemma demonstrates the distributive property of multiplication over subtraction in a non-unital, non-associative ring.
Specifically, it shows that for any elements `x`, `a`, and `b` in such a ring, the expression `x * a - x * b` simplifies to `x * (a - b)`, even in the absence of multiplicative identity or associativity.
-/
lemma Algebra.SubMulS.eq.Mul_Sub
  [NonUnitalNonAssocRing α]
  {x a b : α} :
  x * a - x * b = x * (a - b) := by
  rw [mul_sub]

/--
**Lemma:** If `x` is strictly greater than `y` in a preorder, then `x` is greater than or equal to `y`.
This lemma establishes that a strict inequality (`x > y`) implies the corresponding non-strict inequality (`x ≥ y`) within the context of a preorder.
It leverages the foundational property `Le.of.Lt` to convert between strict and non-strict inequalities, which is essential in ordered algebraic structures.
-/
lemma Algebra.Ge.of.Gt
  [Preorder α]
  {x y : α}
  (h : x > y) :
  x ≥ y := by
  exact Le.of.Lt h

/--
This lemma confirms that in a `SubNegMonoid`, the operation of adding the negation of an element `b` to another element `a` is equivalent to subtracting `b` from `a`.
Specifically, it verifies the algebraic identity `a + (-b) = a - b`, ensuring consistency between additive inverses and subtraction within this algebraic structure.
-/
lemma Algebra.Add_Neg.eq.Sub
  [SubNegMonoid α]
  {a b : α} :
  a + -b = a - b := by
  rw [Sub.eq.Add_Neg]

lemma Algebra.LeMulS.of.Gt_0.Le
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
  (h₀ : x > 0)
  (h₁ : a ≤ b) :
  x * a ≤ x * b := by
  have h := Ge.of.Gt h₀
  apply LeMulS.of.Ge_0.Le h h₁

/--
Given that `x > y` in a preorder, this lemma deduces that `x` and `y` are distinct.
It serves as the symmetric counterpart to `Ne.of.Lt`, utilizing the antisymmetry property inherent in the order relation to establish inequality.
-/
lemma Algebra.Ne.of.Gt
  [Preorder α]
  {x y : α}
  (h : x > y) :
  x ≠ y :=
  (Ne.of.Lt h).symm

/--
This lemma demonstrates the associativity of addition in an additive semigroup, showing that the expression `a + b + c` is equal to `a + (b + c)`.
The proof utilizes the `add_assoc` axiom inherent to the structure of an additive semigroup to rearrange the parentheses, thereby establishing the equality.
-/
lemma Algebra.AddAdd.eq.Add_Add
  [AddSemigroup α]
  {a b : α} :
  a + b + c = a + (b + c) := by
  rw [add_assoc]

lemma Algebra.SquareNeg.eq.Square
  [Ring α]
  {x : α} :
  (-x)² = x² := by
  -- Use the property of additive inverses in rings: (-a) * (-b) = a * b
  rw [sq, sq]
  -- Apply the ring property to show that (-x) * (-x) = x * x
  simp [mul_neg, neg_mul, neg_neg]

lemma Algebra.DivMulS.eq.Div.of.Ne_0
  [Field α]
  {n d a : α}
  (h : a ≠ 0) :
  (n * a) / (d * a) = n / d := by
  -- Step 1: Express division as multiplication by the inverse
  rw [div_eq_mul_inv]
  -- Step 2: Apply the inverse of a product and use commutativity
  rw [mul_inv_rev]
  rw [MulMul.eq.Mul_Mul]
  rw [Mul_Mul.eq.MulMul (a := a)]
  simp [h]
  rw [Div.eq.Mul_Inv]

lemma Algebra.DivNeg.eq.NegDiv
  [DivisionMonoid α] [HasDistribNeg α]
  {a b : α} :
  -a / b = -(a / b) := by
  rw [neg_div]

lemma Algebra.SquareMul.eq.MulSquareS
  [Field α]
  {a b : α} :
  (a * b)² = a² * b² := by
  rw [Square.eq.Mul]
  rw [Mul_Mul.eq.MulMul]
  rw [Mul.comm (a := a * b)]
  rw [Mul_Mul.eq.MulMul]
  rw [Mul.eq.Square]
  rw [MulMul.eq.Mul_Mul]
  rw [Mul.eq.Square]

lemma Algebra.EqMul_Div.of.Ne_0
  [Field α]
  (h : a ≠ 0)
  (b : α) :
  a * (b / a) = b := by
  rw [Mul.comm]
  apply EqMulDiv.of.Ne_0 h

lemma Algebra.SubDivS.eq.DivMul_Sub.of.Ne_0.Ne_0
  [Field α]
  {x a b : α}
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
  x / a - x / b = x * (b - a) / (a * b) := by
  have := SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0 (x := x) (y := x) h₀ h₁
  rw [SubMulS.eq.Mul_Sub] at this
  assumption

lemma Algebra.Mul_Sub.eq.SubMulS.nat
  {x a b : ℕ} :
  x * (a - b) = x * a - x * b := by
  rw [SubMulS.eq.Mul_Sub.nat]

lemma Algebra.Mul_Sub.eq.SubMulS
  [NonUnitalNonAssocRing α]
  {x a b : α} :
  x * (a - b) = x * a - x * b := by
  rw [SubMulS.eq.Mul_Sub]

lemma Algebra.SquareDiv.eq.DivSquareS
  [Field α]
  {a b : α} :
  (a / b)² = a² / b² := by
  rw [Square.eq.Mul]
  rw [Mul_Div.eq.DivMul]
  rw [MulDiv.eq.DivMul]
  rw [Mul.eq.Square]
  rw [DivDiv.eq.Div_Mul]
  rw [Mul.eq.Square]

lemma Algebra.Eq.of.Ge.Le
  [PartialOrder α]
  {a b : α}
  (h₀ : a ≥ b)
  (h₁ : a ≤ b) :
  a = b :=
  Eq.of.Le.Ge h₁ h₀

lemma Algebra.AddNeg.eq.Sub
  [AddCommGroup α]
  {a b : α} :
  -a + b = b - a := by
  rw [Add.comm]
  rw [Sub.eq.Add_Neg]

lemma Algebra.SubSquare_MulMul4.le.Zero.of.Gt_0.AddAddMul_Square.ge.Zero
  {a b c : ℝ}
  (h₀ : a > 0)
  (h₁ : ∀ x : ℝ, a * x² + b * x + c ≥ 0) :
  b² - 4 * a * c ≤ 0 := by
  have := h₁ (-b / (2 * a))
  rw [DivNeg.eq.NegDiv] at this
  rw [SquareNeg.eq.Square] at this
  rw [SquareDiv.eq.DivSquareS] at this
  rw [SquareMul.eq.MulSquareS] at this
  norm_num at this
  rw [Square.eq.Mul (x := a)] at this
  rw [Mul_Mul.eq.MulMul] at this
  rw [Mul_Div.eq.DivMul] at this
  rw [Mul.comm] at this
  have h_Ne := Ne.of.Gt h₀
  rw [DivMulS.eq.Div.of.Ne_0 h_Ne] at this
  rw [Add_Neg.eq.Sub] at this
  rw [Mul_Div.eq.DivMul] at this
  rw [Mul.eq.Square] at this
  rw [SubDivS.eq.DivMul_Sub.of.Ne_0.Ne_0 (by simp [h_Ne] : 4 * a ≠ 0) (by simp [h_Ne] : 2 * a ≠ 0)] at this
  rw [SubMulS.eq.MulSub] at this
  norm_num at this
  rw [NegMul.eq.MulNeg] at this
  rw [DivMulS.eq.Div.of.Ne_0 (by simp [h_Ne] : 2 * a ≠ 0)] at this
  rw [DivNeg.eq.NegDiv] at this
  rw [AddNeg.eq.Sub] at this
  have := LeMulS.of.Gt_0.Le (by simp [h₀] : 4 * a > 0) this
  norm_num at this
  rw [Mul_Sub.eq.SubMulS] at this
  rw [EqMul_Div.of.Ne_0 (by simp [h_Ne] : 4 * a ≠ 0)] at this
  simp_all

lemma Algebra.NotGe.of.Lt
  [PartialOrder α]
  {a b : α}
  (h : a < b) :
  ¬a ≥ b := by
  -- Decompose the strict order into its components: a ≤ b and a ≠ b
  let ⟨_, h⟩ := lt_iff_le_not_le.mp h
  intro h
  contradiction

lemma Algebra.Lt.of.NotGe
  [LinearOrder α]
  {a b : α}
  (h : ¬a ≥ b) :
  a < b := by
  -- Split into cases based on the linear order
  apply lt_iff_le_not_le.mpr
  constructor
  exact le_of_not_ge h
  exact h

/--
This lemma provides the reverse direction of the associativity property for addition in a semigroup, demonstrating that `a + (b + c)` can be rewritten as `a + b + c`.
It complements the `AddAdd.eq.Add_Add` axiom, enabling terms to be regrouped in left-associated form during algebraic proofs.
-/
lemma Algebra.Add_Add.eq.AddAdd
  [AddSemigroup α]
  {a b : α} :
  a + (b + c) = a + b + c := by
  rw [AddAdd.eq.Add_Add]

/--
Given `x > 0` and `a < b`, this lemma proves that `x * a < x * b` by leveraging the strict monotonicity of multiplication by positive elements, as defined by the `PosMulStrictMono` typeclass.
It ensures that multiplying both sides of a strict inequality by a positive element preserves the inequality direction.
-/
lemma Algebra.LtMulS.of.Gt_0.Lt
  [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
  (h1 : x > 0)
  (h2 : a < b) :
  x * a < x * b := by
  exact mul_lt_mul_of_pos_left h2 h1

lemma Algebra.Gt.of.Ge.Ne
  [LinearOrder α]
  {a b : α}
  (h₀ : a ≥ b)
  (h₁ : a ≠ b) :
  a > b := by
  by_contra h
  simp at h
  have := Eq.of.Ge.Le h₀ h
  contradiction

lemma Algebra.Sum_Square.ge.Zero
  {n : ℕ}
  {f : ℕ → ℝ} :
  ∑ i ∈ range n, (f i)² ≥ 0 := by
  -- Use the fact that the sum of non-negative terms is non-negative.
  refine' Finset.sum_nonneg _
  -- Introduce the index variable `i` for the sum.
  intro i _
  -- Each term in the sum is a square of a real number, hence non-negative.
  exact sq_nonneg _

lemma Algebra.SquareAdd.eq.AddAddSquareS_MulMul2
  [CommSemiring α]
  {a b : α} :
  (a + b)² = a² + b² + 2 * a * b :=
  add_sq' a b

lemma Algebra.Gt.of.NotLe
  [LinearOrder α]
  {a b : α}
  (h : ¬a ≤ b) :
  a > b := by
  apply Lt.of.NotGe h

lemma Algebra.GtMulS.of.Gt_0.Gt
  [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
  (h1 : x > 0)
  (h2 : a > b) :
  x * a > x * b :=
  LtMulS.of.Gt_0.Lt h1 h2

lemma Algebra.Sum_SquareAddMul.ge.Zero
  {n : ℕ}
  {x : ℝ}
  {a b : ℕ → ℝ} :
  ∑ i ∈ range n, (a i * x + b i)² ≥ 0 := by
  apply Sum_Square.ge.Zero (f := fun i => a i * x + b i)

lemma Algebra.Sum_Add.eq.AddSumS
  {n : ℕ}
  {a b : ℕ → ℝ} :
  ∑ i ∈ range n, (a i + b i) = ∑ i ∈ range n, a i + ∑ i ∈ range n, b i := by
  induction n with
  | zero =>
    -- Base case: when n = 0, the sum is trivially zero.
    simp
  | succ n ih =>
    -- Inductive step: assume the statement holds for n, prove it for n + 1.
    simp_all [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm]

lemma Algebra.Mul.eq.Zero.is.OrEqS_0
  [MulZeroClass α] [NoZeroDivisors α]
  {a b : α} :
  a * b = 0 ↔ a = 0 ∨ b = 0 :=
  mul_eq_zero

lemma Algebra.Sum_Mul.eq.Mul_Sum
  {n : ℕ}
  {x : ℝ}
  {a : ℕ → ℝ} :
  ∑ i ∈ range n, x * a i = x * ∑ i ∈ range n, a i := by
  induction n with
  | zero =>
    -- Base case: When n = 0, both sums are empty, hence equal to 0.
    simp
  | succ n ih =>
    -- Inductive step: Assume the statement holds for n, prove for n + 1.
    simp_all [Finset.sum_range_succ, mul_add, add_mul]

lemma Algebra.SubSquare_MulMul4.le.Zero.of.Ge_0.AddAddMul_Square.ge.Zero
  {a b c : ℝ}
  (h₀ : ∀ x : ℝ, a * x² + b * x + c ≥ 0)
  (h₁ : a ≥ 0) :
  b² - 4 * a * c ≤ 0 := by
  by_cases h : a = 0
  ·
    rw [h] at h₀
    norm_num at h₀
    rw [h]
    norm_num
    suffices b = 0 by rw [this]; simp
    by_contra h
    have : ∃ t, b * t + c < 0 := by
      use -(c + 1) / b
      rw [EqMul_Div.of.Ne_0 h]
      simp
    let ⟨t, h_t⟩ := this
    have := h₀ t
    linarith
  ·
    have := Gt.of.Ge.Ne h₁ h
    apply SubSquare_MulMul4.le.Zero.of.Gt_0.AddAddMul_Square.ge.Zero this h₀

lemma Algebra.Sum_Mul.eq.MulSum
  {n : ℕ}
  {x : ℝ}
  {a : ℕ → ℝ} :
  ∑ i ∈ range n, a i * x = (∑ i ∈ range n, a i) * x := by
  induction n with
  | zero =>
    -- Base case: When n = 0, both sums are empty, hence equal to 0.
    simp
  | succ n ih =>
    -- Inductive step: Assume the statement holds for n, prove for n + 1.
    simp_all [Finset.sum_range_succ, mul_add, add_mul]

lemma Algebra.NotLe.of.Gt
  [PartialOrder α]
  {a b : α}
  (h : a > b) :
  ¬a ≤ b := by
  apply NotGe.of.Lt h

lemma Algebra.EqSquareSqrt.of.Ge_0
  {x : ℝ}
  (h : x ≥ 0) :
  (√x)² = x :=
  Real.sq_sqrt h

lemma Algebra.AddAdd.comm
  [AddCommSemigroup α]
  {a b : α} :
  a + b + c = a + c + b := by
  rw [Add.comm (b := c)]
  rw [Add.comm (b := c)]
  rw [Add_Add.eq.AddAdd]

lemma Algebra.LeMulS.of.Le.Ge_0
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
  (h1 : a ≤ b)
  (h2 : x ≥ 0) :
  a * x ≤ b * x :=
  mul_le_mul_of_nonneg_right h1 h2

lemma Algebra.OrEqS_0.of.Mul.eq.Zero
  [MulZeroClass α] [NoZeroDivisors α]
  {a b : α}
  (h : a * b = 0) :
  a = 0 ∨ b = 0 := by
  exact Mul.eq.Zero.is.OrEqS_0.mp h

lemma Algebra.NotGt.of.Eq
  [Preorder α]
  {a b : α}
  (h : a = b) :
  ¬a > b := by
  rw [h]
  exact fun hgt => lt_irrefl b hgt

lemma Algebra.EqSquareSqrt.of.Gt_0
  {x : ℝ}
  (h : x > 0) :
  (√x)² = x := by
  have := Ge.of.Gt h
  apply EqSquareSqrt.of.Ge_0 this

/--
This lemma states that in a type `α` equipped with addition and a strict order preserved by both left and right addition (as per the `AddLeftStrictMono` and `AddRightStrictMono` type classes), if `b < c`, then adding an element `a` to either side of `b` and `c` maintains the strict inequality.
The boolean parameter `left` determines the side of addition: when `true`, it yields `a + b < a + c`, and when `false`, it gives `b + a < c + a`.
-/
lemma Algebra.LtAddS.of.Lt
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {b c : α}
  (h : b < c)
  (a : α)
  (left : Bool := false) :
  match left with
  | true => a + b < a + c
  | false => b + a < c + a :=
  match left with
  | true =>
    add_lt_add_left h a
  | false =>
    add_lt_add_right h a

lemma Algebra.AddAddMulSquare_Sum.ge.Zero
  {n : ℕ}
  {x : ℝ}
  {a b : ℕ → ℝ} :
  x² * ∑ i ∈ range n, (a i)² + 2 * x * ∑ i ∈ range n, a i * b i + ∑ i ∈ range n, (b i)² ≥ 0 := by
  have := Sum_SquareAddMul.ge.Zero (n := n) (x := x) (a := a) (b := b)
  simp [SquareAdd.eq.AddAddSquareS_MulMul2] at this
  rw [Sum_Add.eq.AddSumS] at this
  rw [Sum_Add.eq.AddSumS] at this
  simp [SquareMul.eq.MulSquareS] at this
  rw [Sum_Mul.eq.MulSum] at this
  rw [Mul.comm] at this
  rw [AddAdd.comm] at this
  simp [Mul.comm (b := x)] at this
  simp [Mul_Mul.eq.MulMul] at this
  simp [MulMul.eq.Mul_Mul (a := 2 * x)] at this
  rw [Sum_Mul.eq.Mul_Sum] at this
  assumption

lemma Algebra.Square.eq.Zero.of.Eq_0
  {x : ℝ}
  (h : x = 0) :
  x² = 0 := by
  -- Square both sides of the equation
  rw [h]
  -- Calculate the square of 0 and substitute back into the equation
  norm_num

lemma Algebra.Square.ge.Zero
  [Semiring α] [LinearOrder α]
  [IsRightCancelAdd α] [ZeroLEOneClass α] [ExistsAddOfLE α]
  [PosMulMono α] [AddLeftStrictMono α]
  {a : α} :
  a² ≥ 0 :=
  sq_nonneg a

lemma Algebra.Le.of.Gt_0.LeMulS
  [Mul α] [Zero α] [LinearOrder α] [PosMulStrictMono α]
  {x a b : α}
  (h₀ : x > 0)
  (h₁ : x * a ≤ x * b) :
  a ≤ b := by
  by_contra h
  have := Gt.of.NotLe h
  have := GtMulS.of.Gt_0.Gt h₀ this
  have := NotLe.of.Gt this
  contradiction

lemma Algebra.Square.le.MulMul4.of.Ge_0.AddAddMul_Square.ge.Zero
  {a b c : ℝ}
  (h₀ : ∀ x : ℝ, a * x² + b * x + c ≥ 0)
  (h₁ : a ≥ 0) :
  b² ≤ 4 * a * c := by
  have := SubSquare_MulMul4.le.Zero.of.Ge_0.AddAddMul_Square.ge.Zero h₀ h₁
  simp_all

lemma Algebra.Inv.ge.Zero.is.Ge_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {a : α} :
  a⁻¹ ≥ 0 ↔ a ≥ 0 :=
  inv_nonneg

lemma Algebra.EqDivS.of.Eq
  [Div α]
  {x y : α}
  (h : x = y)
  (d : α) :
  x / d = y / d := by
  rw [h]

lemma Algebra.GeMulS.of.Ge.Ge_0
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
  (h1 : a ≥ b)
  (h2 : x ≥ 0) :
  a * x ≥ b * x :=
  LeMulS.of.Le.Ge_0 h1 h2

lemma Algebra.Sqrt.ge.Zero
  {x : ℝ} :
  √x ≥ 0 := by
  -- By definition, the square root of a real number x is only defined for x ≥ 0.
  -- The principal square root of x, denoted √x, is the unique non-negative real number y such that y^2 = x.
  -- Therefore, √x ≥ 0 for all x in the domain x ≥ 0.
  exact Real.sqrt_nonneg x

lemma Algebra.Eq_0.of.Square.eq.Zero
  [LinearOrderedRing α]
  {x : α}
  (h : x² = 0) :
  x = 0 := by
  rw [Square.eq.Mul] at h
  have h := OrEqS_0.of.Mul.eq.Zero h
  cases h <;> assumption

lemma Algebra.Inv.ge.Zero.of.Ge_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {a : α}
  (h : a ≥ 0) :
  a⁻¹ ≥ 0 :=
  Inv.ge.Zero.is.Ge_0.mpr h

lemma Algebra.Sqrt.ne.Zero.of.Gt_0
  {x : ℝ}
  (h : x > 0) :
  √x ≠ 0 := by
  -- Assume for contradiction that √x = 0
  intro h₁
  have h_Eq_0 := Square.eq.Zero.of.Eq_0 h₁
  have := EqSquareSqrt.of.Gt_0 h
  rw [this] at h_Eq_0
  have := NotGt.of.Eq h_Eq_0
  contradiction

lemma Algebra.Sqrt.eq.Zero.of.Le_0
  {x : ℝ}
  (h : x ≤ 0) :
  √x = 0 :=
  Real.sqrt_eq_zero_of_nonpos h

lemma Algebra.Square.ne.Zero.of.Ne_0
  [LinearOrderedRing α]
  {a : α}
  (h : a ≠ 0) :
  a² ≠ 0 := by
  by_contra h'
  rw [Square.eq.Mul] at h'
  have h := OrEqS_0.of.Mul.eq.Zero h'
  simp at h
  contradiction

/--
This lemma establishes the equivalence between multiplication by the inverse and division in a `DivInvMonoid`, serving as the reverse of `Div.eq.Mul_Inv`.
It simplifies expressions by allowing the interchange of `a * b⁻¹` and `a / b` within the algebraic structure `α`.
-/
lemma Algebra.Mul_Inv.eq.Div
  [DivInvMonoid α]
  {a b : α} :
  a * b⁻¹ = a / b := by
  rw [Div.eq.Mul_Inv]

/--
Given an ordered additive commutative group `α`, if `x < y` for elements `x, y : α`, then subtracting the same element `z : α` from both `x` and `y` preserves the inequality.
Specifically, `x - z < y - z`.
This follows by expressing subtraction as addition of the negation and applying the property that addition preserves strict order.
-/
lemma Algebra.LtSubS.of.Lt
  [OrderedAddCommGroup α]
  {x y : α}
  (h : x < y)
  (z : α) :
  x - z < y - z := by
  rw [Sub.eq.Add_Neg (a := x), Sub.eq.Add_Neg (a := y)]
  apply LtAddS.of.Lt h (-z)

lemma Algebra.SquareSum_Mul.le.MulSumS_Square.cauchy_schwarz
  {n : ℕ}
  {a b : ℕ → ℝ} :
  (∑ i ∈ range n, a i * b i)² ≤ (∑ i ∈ range n, (a i)²) * ∑ i ∈ range n, (b i)² := by
  let A := ∑ i ∈ range n, (a i)²
  have hA : A = ∑ i ∈ range n, (a i)² := rfl
  let B := 2 * ∑ i ∈ range n, a i * b i
  have hB : B = 2 * ∑ i ∈ range n, a i * b i := rfl
  have hB := EqDivS.of.Eq hB 2
  norm_num at hB
  let C := ∑ i ∈ range n, (b i)²
  have hC : C = ∑ i ∈ range n, (b i)² := rfl
  rw [← hA, ← hC, ← hB]
  rw [SquareDiv.eq.DivSquareS]
  norm_num
  apply Le.of.Gt_0.LeMulS (by norm_num : (4 : ℝ) > 0)
  rw [Mul_Mul.eq.MulMul]
  rw [EqMul_Div.of.Ne_0 (by norm_num : (4 : ℝ) ≠ 0)]
  apply Square.le.MulMul4.of.Ge_0.AddAddMul_Square.ge.Zero
  ·
    intro x
    have := AddAddMulSquare_Sum.ge.Zero (n := n) (x := x) (a := a) (b := b)
    rw [← hA, ← hC, ← hB] at this
    rw [Mul.comm (a := 2)] at this
    rw [MulMul.eq.Mul_Mul] at this
    rw [EqMul_Div.of.Ne_0 (by norm_num : (2 : ℝ) ≠ 0)] at this
    rw [Mul.comm] at this
    rw [Mul.comm (a := x)] at this
    assumption
  ·
    have hA := Sum_Square.ge.Zero (n := n) (f := a)
    assumption

lemma Algebra.Le.of.NotGt
  [LinearOrder α]
  {a b : α}
  (h : ¬a > b) :
  a ≤ b := by
  apply not_lt.mp h

lemma Algebra.Square.gt.Zero.of.Ne_0
  [LinearOrderedRing α]
  {a : α}
  (h : a ≠ 0) :
  a² > 0 :=
  Gt.of.Ge.Ne
    (Square.ge.Zero (a := a))
    (Square.ne.Zero.of.Ne_0 h)

lemma Algebra.LeSumS.of.All_Le
  {n : ℕ}
  {x y : ℕ → ℝ}
  (h₀ : ∀ i ∈ range n, x i ≤ y i) :
  ∑ i ∈ range n, x i ≤ ∑ i ∈ range n, y i := by
  -- Use the fact that the sum of non-negative terms is non-negative.
  refine' Finset.sum_le_sum fun i hi => _
  -- Apply the given inequality for each i in the range.
  exact h₀ i hi

/--
This lemma establishes that in a group with zero `α` equipped with a partial order and satisfying `ZeroLEOneClass` and `PosMulReflectLT`, the inverse of an element `x` is positive if and only if `x` itself is positive.
It serves as a simplification rule to handle inequalities involving inverses in ordered algebraic structures.
-/
lemma Algebra.Inv.gt.Zero.is.Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α} :
  x⁻¹ > 0 ↔ x > 0 :=
  inv_pos

lemma Algebra.GeDivS.of.Ge.Ge_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
  (h₀ : a ≥ b)
  (h₁ : x ≥ 0) :
  a / x ≥ b / x := by
  have : x⁻¹ ≥ 0 := Inv.ge.Zero.of.Ge_0 h₁
  have := GeMulS.of.Ge.Ge_0 h₀ this
  rw [
    Mul_Inv.eq.Div,
    Mul_Inv.eq.Div
  ] at this
  exact this

lemma Algebra.Div0.eq.Zero
  [GroupWithZero α]
  {a : α} :
  0 / a = 0 := by
  apply zero_div

lemma Algebra.Add_Sub.eq.SubAdd
  [SubNegMonoid α]
  {a b c : α} :
  a + (b - c) = a + b - c := by
  rw [add_sub_assoc]

lemma Algebra.Ge.of.Ge.Ge
  [Preorder α]
  {a b c : α}
  (h₀ : a ≥ b)
  (h₁ : b ≥ c) :
  a ≥ c :=
  ge_trans h₀ h₁

lemma Algebra.Eq_0.of.Square.le.Zero
  [LinearOrderedRing α]
  {x : α}
  (h : x² ≤ 0) :
  x = 0 := by
  have := Square.ge.Zero (a := x)
  have := Eq.of.Le.Ge h this
  apply Eq_0.of.Square.eq.Zero this

/--
In any additive group `α`, subtracting an element `a` from itself yields the additive identity `0`.
This fundamental property, expressed as `a - a = 0`, is essential for simplifying expressions and streamlining proofs involving group operations.
-/
lemma Algebra.Sub.eq.Zero
  [AddGroup α]
  {a : α} :
  a - a = 0 := by
  rw [sub_self]

/--
In an additive commutative group, the expression \(a - b + c\) is equivalent to \(a + c - b\).
This lemma demonstrates that subtraction and addition can be reordered while preserving equality, leveraging the commutativity and associativity of the group operation.
The proof systematically applies fundamental group axioms to rearrange terms and verify the equivalence.
-/
lemma Algebra.AddSub.eq.SubAdd
  [AddCommGroup α]
  {a b c : α} :
  a - b + c = a + c - b := by
  rw [Sub.eq.Add_Neg]
  rw [AddAdd.eq.Add_Add]
  rw [Add.comm (b := c)]
  rw [Add_Add.eq.AddAdd]
  rw [Add_Neg.eq.Sub]

lemma Algebra.Sqrt.eq.Zero.of.Lt_0
  {x : ℝ}
  (h : x < 0) :
  √x = 0 := by
  have := Le.of.Lt h
  apply Sqrt.eq.Zero.of.Le_0 this

lemma Algebra.Sqrt.gt.Zero.of.Gt_0
  {x : ℝ}
  (h : x > 0) :
  √x > 0 := by
  have := Sqrt.ge.Zero (x := x)
  have h_Ne := Sqrt.ne.Zero.of.Gt_0 h
  exact Gt.of.Ge.Ne this h_Ne

lemma Algebra.EqSumS.of.All_Eq
  [AddCommMonoid β]
  {s : Finset ι}
  {x y : ι → β}
  (h : ∀ i ∈ s, x i = y i) :
  ∑ i ∈ s, x i = ∑ i ∈ s, y i := by
  -- We use the fact that the sum of a sequence is uniquely determined by its elements.
  -- Since for all i in the range n, x i = y i, we can directly substitute x with y in the sum.
  rw [Finset.sum_congr rfl fun i hi => h i hi]

lemma Algebra.GtSubS.of.Gt
  [OrderedAddCommGroup α]
  {x y : α}
  (h : x > y)
  (z : α) :
  x - z > y - z :=
  LtSubS.of.Lt h z

lemma Logic.All.of.All.All_Imp.binary
  {s : Finset ι}
  {x : ι → α}
  {p q : α → ι → Prop}
  (h₀ : ∀ (t : α) (i : ι), p t i → q t i)
  (h₁ : ∀ i ∈ s, p (x i) i) :
  ∀ i ∈ s, q (x i) i := by
  -- Introduce the universal quantifier and the assumption that i is in the range n
  intro i hi
  -- Provide the proof of p (x i) using h₀ with the given index i and its range membership hi
  have := h₁ i hi
  -- Apply the implication h₁ to transform the goal into proving p (x i)
  apply h₀ (x i) i this

lemma Logic.All.of.All.All_Imp
  {s : Finset ι}
  {x : ι → α}
  {p q : α → Prop}
  (h₀ : ∀ t : α, p t → q t)
  (h₁ : ∀ i ∈ s, p (x i)) :
  ∀ i ∈ s, q (x i) := by
  -- Introduce the universal quantifier and the assumption that i is in the range n
  intro i hi
  -- Provide the proof of p (x i) using h₀ with the given index i and its range membership hi
  have := h₁ i hi
  -- Apply the implication h₁ to transform the goal into proving p (x i)
  apply h₀ (x i) this

lemma Algebra.SquareSum.le.Mul_Sum_Square.cauchy_schwarz
  {n : ℕ}
  {x : ℕ → ℝ} :
  (∑ i ∈ range n, x i)² ≤ n * ∑ i ∈ range n, (x i)² := by
  have := SquareSum_Mul.le.MulSumS_Square.cauchy_schwarz (n := n) (a := x) (b := fun i => 1)
  norm_num at this
  rw [Mul.comm] at this
  assumption

lemma Algebra.Ge.of.NotLt
  [LinearOrder α]
  {a b : α}
  (h : ¬a < b) :
  a ≥ b :=
  Le.of.NotGt h

lemma Algebra.Sqrt.eq.Root_2
  {x : ℝ} :
  √x = x ^ (1 / 2 : ℝ) :=
  -- Use the property of exponents to simplify the expression
  Real.sqrt_eq_rpow x

lemma Algebra.EqAdd0.nat
  [AddZeroClass R]
  [AddMonoidWithOne R]
  [Nat.AtLeastTwo a] :
  (Nat.cast 0 : R) + OfNat.ofNat a = OfNat.ofNat a := by
  simp [zero_add]

lemma Algebra.EqAdd0
  [AddZeroClass R]
  {a : R} :
  0 + a = a := by
  rw [zero_add]

lemma Algebra.GeMulS.of.Ge.Gt_0
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
  (h1 : a ≥ b)
  (h2 : x > 0) :
  a * x ≥ b * x := by
  have h := Ge.of.Gt h2
  apply GeMulS.of.Ge.Ge_0 h1 h

lemma Algebra.SquareSum_Sqrt.le.Mul_Sum.of.All_Ge_0.cauchy_schwarz
  {n : ℕ}
  {x : ℕ → ℝ}
  (h : ∀ i ∈ range n, x i ≥ 0) :
  (∑ i ∈ range n, √(x i))² ≤ n * ∑ i ∈ range n, x i := by
  have h_Le := SquareSum.le.Mul_Sum_Square.cauchy_schwarz (n := n) (x := fun i => √(x i))
  have : ∀ t : ℝ, t ≥ 0 → (√t)² = t := by
    intro t h
    apply EqSquareSqrt.of.Ge_0 h
  have := All.of.All.All_Imp this h
  have := EqSumS.of.All_Eq this
  rw [this] at h_Le
  assumption

lemma Algebra.GeSumS.of.All_Ge
  {n : ℕ}
  {x y : ℕ → ℝ}
  (h₀ : ∀ i ∈ range n, x i ≥ y i) :
  ∑ i ∈ range n, x i ≥ ∑ i ∈ range n, y i := by
  exact LeSumS.of.All_Le (n := n) (x := y) (y := x) h₀

lemma Algebra.EqAddS.of.Eq.left
  [Add α]
  {x y : α}
  (h : x = y)
  (d : α) :
  d + x = d + y := by
  rw [h]

lemma Algebra.EqAddS.of.Eq
  [Add α]
  {x y : α}
  (h : x = y)
  (d : α) :
  x + d = y + d := by
  rw [h]

lemma Algebra.LeAdd_1.of.Lt
  [IntegerRing α]
  {x y : α}
  (h : x < y) :
  x + 1 ≤ y :=
  IntegerRing.succ_le_of_lt h

/--
This lemma demonstrates that in an additive commutative group, subtracting a subtraction expression `b - c` from `a` is equivalent to first subtracting `b` from `a` and then adding `c`.
The proof leverages the property `sub_sub_eq_add_sub` to rewrite `a - (b - c)` as `a + c - b`, followed by applying `AddSub.eq.SubAdd` to rearrange the terms into the final form `a - b + c`.
-/
lemma Algebra.Sub_Sub.eq.AddSub
  -- [SubtractionMonoid α]
  [AddCommGroup α]
  {a b c : α} :
  a - (b - c) = a - b + c := by
  rw [sub_sub_eq_add_sub]
  rw [AddSub.eq.SubAdd]

lemma Algebra.GeMulS.of.Ge_0.Ge
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
  (h1 : x ≥ 0)
  (h2 : a ≥ b) :
  x * a ≥ x * b :=
  LeMulS.of.Ge_0.Le h1 h2

lemma Algebra.GtSqrtS.of.Gt.Gt_0
  {x y : ℝ}
  (h₀ : x > y)
  (h₁ : x > 0) :
  √x > √y := by
  by_cases h : y < 0
  ·
    have := Sqrt.eq.Zero.of.Lt_0 h
    rw [this]
    apply Sqrt.gt.Zero.of.Gt_0 h₁
  ·
    have h := Ge.of.NotLt h
    -- Use the fact that the square root function is increasing on the positive real numbers.
    apply Real.lt_sqrt_of_sq_lt
    have := EqSquareSqrt.of.Ge_0 h
    rw [this]
    assumption

lemma Set.Lt.of.Mem_Range
  {n i : ℕ}
  (h : i ∈ Finset.range n) :
  i < n := by
  rw [Finset.mem_range] at h
  -- After the rewrite, `h` directly provides the conclusion `i < n`, so we can use it to finish the proof.
  exact h

lemma Algebra.SubAdd.eq.Add_Sub
  [SubNegMonoid α]
  {a b c : α} :
  a + b - c = a + (b - c) := by
  rw [Add_Sub.eq.SubAdd]

lemma Algebra.Gt.of.Gt.Ge
  [Preorder α]
  {a b c : α}
  (h₀ : a > b)
  (h₁ : b ≥ c) :
  a > c :=
  gt_of_gt_of_ge h₀ h₁

lemma Algebra.SubAdd.eq.AddSub
  [AddCommGroup α]
  {a b c : α} :
  a + b - c = a - c + b := by
  rw [AddSub.eq.SubAdd]

lemma Algebra.Le_Sqrt.of.LeSquare
  {x : ℝ}
  (h : x² ≤ y) :
  x ≤ √y := by
  -- We need to show that x ≤ √y given x² ≤ y. We consider two cases: x ≥ 0 and x < 0.
  cases' le_total 0 x with hx hx
  ·
    -- For each case, we use the fact that the square root of a non-negative number is non-negative.
    cases' le_total 0 y with hy hy
    ·
      -- Case 1: x ≥ 0 and y ≥ 0
      -- Since x ≥ 0 and y ≥ 0, we can take the square root of both sides of x² ≤ y.
      apply (Real.le_sqrt hx hy).mpr h
    ·
      -- Case 2: x ≥ 0 and y < 0
      -- This case is impossible because y < 0 contradicts x² ≤ y (since x² is always non-negative).
      have := Square.ge.Zero (a := x)
      have := Ge.of.Ge.Ge h this
      have := Eq.of.Le.Ge hy this
      rw [this]
      rw [this] at h
      norm_num
      have := Eq_0.of.Square.le.Zero h
      linarith
  ·
    have := Sqrt.ge.Zero (x := y)
    linarith

lemma Logic.Ne.of.NotEq
  {a b : α}
  (h : ¬a = b) :
  a ≠ b := by
  exact h

lemma Algebra.Eq.ou.Lt.of.Le
  [PartialOrder α]
  {a b : α}
  (h : a ≤ b) :
  a = b ∨ a < b :=
  eq_or_lt_of_le h

lemma Algebra.NotGt
  [Preorder α]
  {a : α} :
  ¬(a > a) :=
  gt_irrefl a

lemma Algebra.EqSqrtSquare.of.Ge_0
  {x : ℝ}
  (h : x ≥ 0) :
  √x² = x :=
  Real.sqrt_sq h

lemma Algebra.Sub.gt.Zero.of.Gt
  [OrderedAddCommGroup α]
  {x y : α}
  (h : x > y) :
  x - y > 0 := by
  have := GtSubS.of.Gt h y
  rw [Sub.eq.Zero] at this
  assumption

lemma Algebra.Div.ge.Zero.of.Ge_0.Ge_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {a b : α}
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
  a / b ≥ 0 := by
  have h := GeDivS.of.Ge.Ge_0 h₀ h₁
  simp only [Div0.eq.Zero] at h
  exact h

/--
This lemma states that in a group with zero `α` equipped with a partial order and satisfying `ZeroLEOneClass` and `PosMulReflectLT` properties, if an element `x` is positive (`x > 0`), then its multiplicative inverse `x⁻¹` is also positive.
The proof follows directly from the equivalence `Inv.gt.Zero.is.Gt_0` which establishes the bidirectional implication between `x > 0` and `x⁻¹ > 0`.
-/
lemma Algebra.Inv.gt.Zero.of.Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α}
  (h : x > 0) :
  x⁻¹ > 0 :=
  Inv.gt.Zero.is.Gt_0.mpr h

lemma Algebra.SquareSub.eq.SubAddSquareS_MulMul2
  [Field α]
  {a b : α} :
  (a - b)² = a² + b² - 2 * a * b := by
  rw [
    Sub.eq.Add_Neg,
    SquareAdd.eq.AddAddSquareS_MulMul2
  ]
  simp [Sub.eq.Add_Neg]

lemma Algebra.Square.gt.Zero.of.Gt_0
  [LinearOrderedRing α]
  {a : α}
  (h : a > 0) :
  a² > 0 := by
  have := Ne.of.Gt h
  apply Square.gt.Zero.of.Ne_0 this

lemma Algebra.MulSub_1.eq.SubMul.nat
  {x a : ℕ} :
  (a - 1) * x = a * x - x := by
  rw [MulSub.eq.SubMulS.nat]
  simp

lemma Algebra.MulSub_1.eq.SubMul
  [Ring α]
  {x a : α} :
  (a - 1) * x = a * x - x := by
  rw [MulSub.eq.SubMulS]
  simp

lemma Algebra.AddMulS.eq.Mul_Add
  [Mul α] [Add α] [LeftDistribClass α]
  {x a b : α} :
  x * a + x * b = x * (a + b) := by
  rw [mul_add]

/--
This lemma asserts that in a field, multiplying an element `b` by a non-zero element `a` and then dividing by `a` yields `b`, with the order of multiplication determined by the `comm` flag.
When `comm` is `true`, the multiplication is `a * b`, and when `false`, it is `b * a`, but in both cases, division by `a` cancels out the multiplication due to `a` being non-zero.
-/
lemma Algebra.EqDivMul.of.Ne_0
  [Field α]
  {a b : α}
  (h : a ≠ 0)
  (comm : Bool := false) :
  match comm with
  | true => a * b / a = b
  | false => b * a / a = b := by
  cases comm <;>
    simp [h]

lemma Algebra.GtAddS.of.Gt
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {b c : α}
  (h : b > c)
  (a : α)
  (left : Bool := false) :
  match left with
  | true =>
    a + b > a + c
  | false =>
    b + a > c + a :=
  match left with
  | true =>
    LtAddS.of.Lt h a true
  | false =>
    LtAddS.of.Lt h a

lemma Algebra.Mul_0.eq.Zero
  [MulZeroClass α]
  {a : α} :
  a * 0 = 0 := by
  apply MulZeroClass.mul_zero

lemma Algebra.Sum_Sqrt.le.SqrtMul_Sum.of.All_Ge_0.cauchy_schwarz
  {n : ℕ}
  {x : ℕ → ℝ}
  (h : ∀ i ∈ range n, x i ≥ 0) :
  ∑ i ∈ range n, √(x i) ≤ √(n * ∑ i ∈ range n, x i) := by
  have := SquareSum_Sqrt.le.Mul_Sum.of.All_Ge_0.cauchy_schwarz (n := n) (x := x) h
  have := Le_Sqrt.of.LeSquare this
  assumption

lemma Algebra.Sum.ge.Zero.of.All_Ge_0
  {n : ℕ}
  {x : ℕ → ℝ}
  (h : ∀ i ∈ range n, x i ≥ 0) :
  ∑ i ∈ range n, (x i) ≥ 0 := by
  have := GeSumS.of.All_Ge (n := n) (x := x) (y := fun _ => 0) h
  simp at this
  assumption

lemma Algebra.GeDivS.of.Ge.Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
  (h₀ : a ≥ b)
  (h₁ : x > 0) :
  a / x ≥ b / x := by
  have : x⁻¹ > 0 := Inv.gt.Zero.of.Gt_0 h₁
  have := GeMulS.of.Ge.Gt_0 h₀ this
  rw [
    Mul_Inv.eq.Div,
    Mul_Inv.eq.Div
  ] at this
  assumption

lemma Algebra.Mul.ge.Zero.of.Ge_0.Ge_0
  [MulZeroClass α] [Preorder α] [PosMulMono α]
  {a b : α}
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
  a * b ≥ 0 := by
  have h := GeMulS.of.Ge_0.Ge h₀ h₁
  simp only [Mul_0.eq.Zero] at h
  exact h

/--
This lemma demonstrates that in an additive commutative group, the order of subtraction of two elements does not affect the result.
Specifically, it shows that subtracting `b` and then `c` from `a` yields the same value as subtracting `c` and then `b`, leveraging the commutativity of the group operation.
-/
lemma Algebra.SubSub.comm
  [AddCommGroup α]
  {a b c : α} :
  a - b - c = a - c - b := by
  abel

lemma Algebra.EqSub_Sub
  [AddCommGroup α]
  {a b : α} :
  a - (a - b) = b := by
  rw [Sub_Sub.eq.AddSub]
  rw [Sub.eq.Zero]
  rw [EqAdd0]

lemma Logic.AndAnd.is.And_And :
  (p ∧ q) ∧ r ↔ p ∧ q ∧ r :=
  and_assoc

/--
This lemma states that in a preorder, if `a` is less than or equal to `b` (`a ≤ b`) and `b` is strictly less than `c` (`b < c`), then `a` is strictly less than `c` (`a < c`).
It demonstrates the transitivity of the strict less-than relation under the given preorder constraints.
-/
lemma Algebra.Lt.of.Le.Lt
  [Preorder α]
  {a b c : α}
  (h₀ : a ≤ b)
  (h₁ : b < c) :
  a < c :=
  lt_of_le_of_lt h₀ h₁

lemma Algebra.AddSub.eq.Add_Sub
  [AddCommGroup α]
  {a b c : α} :
  a - b + c = a + (c - b) := by
  rw [AddSub.eq.SubAdd]
  rw [SubAdd.eq.Add_Sub]

lemma Algebra.Mul.gt.Zero.of.Gt_0.Gt_0
  [MulZeroClass α] [Preorder α] [PosMulStrictMono α]
  {a b : α}
  (h₀ : a > 0)
  (h₁ : b > 0) :
  a * b > 0 := by
  have h := GtMulS.of.Gt_0.Gt h₀ h₁
  simp only [Mul_0.eq.Zero] at h
  exact h

lemma Algebra.AddSub_Mul2Sqrt.gt.Zero.of.Gt_1
  {x : ℝ}
  (h : x > 1) :
  x - 2 * √x + 1 > 0 := by
  have := SquareSub.eq.SubAddSquareS_MulMul2 (a := √x) (b := 1)
  norm_num at this
  have h_Sqrt := GtSqrtS.of.Gt.Gt_0 h (by linarith [h])
  norm_num at h_Sqrt
  have h_Sqrt := Sub.gt.Zero.of.Gt h_Sqrt
  have h_Gt_0 := Square.gt.Zero.of.Gt_0 (a := √x - 1) h_Sqrt
  rw [this] at h_Gt_0
  have := EqSquareSqrt.of.Gt_0 (by linarith [h] : x > 0)
  rw [this] at h_Gt_0
  rw [SubAdd.eq.AddSub] at h_Gt_0
  assumption

lemma Algebra.EqSubAdd.int
  [IntegerRing Z]
  {a b : Z}
  (left : Bool := false) :
  match left with
  | true =>
    b + a - b = a
  | false =>
    a + b - b = a := by
  match left with
  | true =>
    have := IntegerRing.add_sub_cancel a b
    rw [Add.comm] at this
    assumption
  | false =>
    apply IntegerRing.add_sub_cancel

lemma Algebra.EqSubAdd.left
  [AddCommGroup α]
  {a b : α} :
  a + b - a = b := by
  apply add_sub_cancel_left

lemma Algebra.EqSubAdd
  [AddGroup α]
  {a b : α} :
  a + b - b = a := by
  apply add_sub_cancel_right

lemma Algebra.Gt_0.of.Ne_0
  {n : ℕ}
  (h : n ≠ 0) :
  n > 0 := by
  exact Nat.pos_of_ne_zero h

lemma Algebra.All_Le.of.All_Le.All_Eq_Ite
  {n i' : ℕ}
  {x y y' : ℕ → ℝ}
  (h₀ : i' ∈ range n)
  (h₁ : ∀ i ∈ range n, x i ≤ y i)
  (h₂ : ∀ i ∈ range n, y' i = ite (i = i') (x i) (y i)) :
  ∀ i ∈ range n, x i ≤ y' i := by
  intro i h_In
  by_cases h : i = i'
  ·
    rw [h]
    have := h₂ i' h₀
    simp at this
    linarith
  ·
    have h := Ne.of.NotEq h
    have := h₂ i h_In
    simp [h] at this
    rw [this]
    exact h₁ i h_In

lemma Algebra.Sum.eq.Sum_Add_Sub.of.Mem_Range.All_Eq_Ite
  {n i' : ℕ}
  {x y y' : ℕ → ℝ}
  (h₀ : i' ∈ range n)
  (h₁ : ∀ i ∈ range n, y' i = ite (i = i') (x i) (y i)) :
  ∑ i ∈ range n, y' i = (∑ i ∈ range n, y i) + (x i' - y i') := by
  have := EqSumS.of.All_Eq h₁
  rw [Finset.sum_ite] at this
  have h_Lt := Lt.of.Mem_Range h₀
  simp [h₀, h_Lt] at this
  rw [this]
  rw [Add.comm]
  rw [Add_Sub.eq.SubAdd]
  rw [SubAdd.eq.AddSub]
  apply EqAddS.of.Eq (d := x i')
  rw [Finset.sum_filter]
  -- Apply the given lemma to the piecewise defined sequence y'
  -- Simplify the sum by splitting it into the case where i = i' and i ≠ i'
  simp [h₀, h_Lt]
  let y'' := fun i => ite (i = i') (y i) (y i)
  have h_y'' : ∀ i ∈ range n, y'' i = ite (i = i') (y i) (y i) := by
    intro i hi
    by_cases h : i = i'
    ·
      rw [h]
    ·
      unfold y''
      simp [h]
  have h_Eq : ∀ i ∈ range n, y'' i = (y i) := by
    simp at h_y''
    intro i hi
    have hi := Lt.of.Mem_Range hi
    exact h_y'' i hi
  have h_Eq := EqSumS.of.All_Eq h_Eq
  have := EqSumS.of.All_Eq h_y''
  have := Eq.trans h_Eq.symm this
  rw [Finset.sum_ite] at this
  rw [this]
  rw [Finset.sum_filter]
  simp [h₀, h_Lt]
  rw [Finset.sum_filter]
  simp [h₀, h_Lt]

/--
In an ordered additive commutative group, if an element `x` is less than another element `y`, then the difference `x - y` is negative.
This lemma leverages the order-preserving property of subtraction and the inverse element axiom to establish that `x - y < 0` under the given condition.
-/
lemma Algebra.Sub.lt.Zero.of.Lt
  [OrderedAddCommGroup α]
  {x y : α}
  (h : x < y) :
  x - y < 0 := by
  have := LtSubS.of.Lt h y
  rw [Sub.eq.Zero] at this
  assumption

lemma Algebra.Mul_Add.eq.AddMulS
  [Mul α] [Add α] [LeftDistribClass α]
  {x a b : α} :
  x * (a + b) = x * a + x * b := by
  rw [AddMulS.eq.Mul_Add]

lemma Algebra.Lt.of.Sub.gt.Zero
  [OrderedAddCommGroup α]
  {x y : α}
  (h : y - x > 0) :
  x < y := by
  have := LtAddS.of.Lt h x
  simp at this
  assumption

lemma Algebra.Root_Add_2.le.Sqrt.of.Ge_1
  {x : ℝ}
  {i : ℕ}
  (h : x ≥ 1) :
  x ^ (1 / (i + 2) : ℝ) ≤ √x := by
  -- We need to show that x^(1/(i+2)) ≤ x^(1/2) for x ≥ 1 and i a natural number.
  -- First, note that i + 2 ≥ 3 since i is a natural number.
  -- Therefore, 1/(i+2) ≤ 1/3 < 1/2.
  -- For x ≥ 1, the function f(k) = x^k is increasing.
  -- Hence, x^(1/(i+2)) ≤ x^(1/2).
  rw [Sqrt.eq.Root_2]
  -- Use the property that for x ≥ 1, the function x^k is increasing.
  -- This allows us to compare the exponents directly.
  apply Real.rpow_le_rpow_of_exponent_le h
  -- Show that 1/(i+2) ≤ 1/2 for all natural numbers i.
  rw [div_le_div_iff₀]
  ·
    norm_num
  ·
    linarith
  ·
    norm_num

lemma Algebra.Lt.ou.Eq.of.Le
  [PartialOrder α]
  {a b : α}
  (h : a ≤ b) :
  a < b ∨ a = b := by
  rw [Or.comm]
  apply Eq.ou.Lt.of.Le h

lemma Algebra.EqMulS.of.Eq.left
  [Mul α]
  {x y : α}
  (h : x = y)
  (d : α) :
  d * x = d * y := by
  rw [h]

lemma Algebra.EqMulS.of.Eq
  [Mul α]
  {x y : α}
  (h : x = y)
  (d : α) :
  x * d = y * d := by
  rw [h]

lemma Algebra.Mul_Mul.comm
  [CommSemigroup G]
  (a b c : G) :
  a * (b * c) = b * (a * c) :=
  mul_left_comm a b c

lemma Algebra.Div.ge.Zero.of.Ge_0.Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {a b : α}
  (h₀ : a ≥ 0)
  (h₁ : b > 0) :
  a / b ≥ 0 := by
  have := Ge.of.Gt h₁
  apply Div.ge.Zero.of.Ge_0.Ge_0 h₀ this

lemma Algebra.EqDivSquare
  [Field α]
  {x : α} :
  x² / x = x := by
  rw [Square.eq.Mul]
  by_cases h : x = 0
  ·
    rw [h]
    norm_num
  ·
    rw [EqDivMul.of.Ne_0 h]

lemma Algebra.Sub_Add.eq.SubSub.nat
  {a b c : ℕ} :
  a - (b + c) = a - b - c := by
  rw [Nat.sub_add_eq]

lemma Algebra.Sub_Add.eq.SubSub
  [SubtractionCommMonoid α]
  {a b c : α} :
  a - (b + c) = a - b - c := by
  rw [sub_add_eq_sub_sub]

lemma Algebra.EqAddSub.of.Le
  {n m : ℕ}
  (h : m ≤ n) :
  n - m + m = n :=
  Nat.sub_add_cancel h

lemma Algebra.Lt.of.Eq_Add.Lt_0
  [LinearOrderedField α]
  {a b c : α}
  (h₀ : c = a + b)
  (h₁ : b < 0) :
  c < a := by
  linarith [h₀, h₁]

lemma Algebra.Le.of.Lt_Add_1
  [IntegerRing Z]
  {x y : Z}
  (h : x < y + 1) :
  x ≤ y := by
  have h_Le := LeAdd_1.of.Lt h
  by_contra h'
  have := Gt.of.NotLe h'
  have : x + 1 > y + 1 := GtAddS.of.Gt this (a := 1)
  have := Gt.of.Gt.Ge this h_Le
  have := Algebra.NotGt (a := x + 1)
  contradiction

lemma Algebra.SqrtMulSquareS.eq.Mul.of.Ge_0.Ge_0
  {x y : ℝ}
  (h₀ : x ≥ 0)
  (h₁ : y ≥ 0) :
  √(x² * y²) = x * y := by
  have := Square.ge.Zero (a := x)
  have := Real.sqrt_mul this y²
  rw [EqSqrtSquare.of.Ge_0 h₀, EqSqrtSquare.of.Ge_0 h₁] at this
  assumption

lemma Algebra.Lt.of.LtSquareS.Ge_0
  {a b : ℝ}
  (h₀ : a² < b²)
  (h₁ : b ≥ 0) :
  a < b := by
  -- Apply the square root to both sides of the inequality a^2 < b^2
  apply lt_of_pow_lt_pow_left₀ 2 (by linarith) (by linarith)

lemma Algebra.SubMul.eq.MulSub_1.nat
  {x a : ℕ} :
  a * x - x = (a - 1) * x := by
  rw [MulSub_1.eq.SubMul.nat]

lemma Algebra.SubMul.eq.MulSub_1
  [Ring α]
  {x a : α} :
  a * x - x = (a - 1) * x := by
  rw [MulSub_1.eq.SubMul]

lemma Logic.All_EqFunS.of.All_Eq.list
  {s : List α}
  {a b : α → β}
  {f : β → γ}
  (h : ∀ i ∈ s, a i = b i) :
  ∀ i ∈ s, f (a i) = f (b i) := by
  intro i i_in_s
  rw [h i i_in_s]

lemma Logic.All_EqFunS.of.All_Eq.binary
  {s : Finset ι}
  {a b : ι → α}
  {f : α → ι → β}
  (h : ∀ i ∈ s, a i = b i) :
  ∀ i ∈ s, f (a i) i = f (b i) i := by
  intro i i_in_s
  rw [h i i_in_s]

lemma Logic.All_EqFunS.of.All_Eq
  {s : Finset α}
  {a b : α → β}
  {f : β → γ}
  (h : ∀ i ∈ s, a i = b i) :
  ∀ i ∈ s, f (a i) = f (b i) := by
  intro i i_in_s
  rw [h i i_in_s]

lemma Algebra.Root_2.eq.Sqrt
  {x : ℝ} :
  x ^ (1 / 2 : ℝ) = √x := by
  -- Use the property of exponents to simplify the expression
  rw [Sqrt.eq.Root_2]

lemma Algebra.All_LeRoot_Sqrt.of.All_Ge_1
  {n : ℕ}
  {x : ℕ → ℝ}
  (h₁ : ∀ i ∈ range n, x i ≥ 1) :
  ∀ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) ≤ √(x i) := by
  have : ∀ (t : ℝ) (i : ℕ), t ≥ 1 → (t ^ (1 / (i + 2) : ℝ) ≤ √t) := by
    intro t i h
    apply Root_Add_2.le.Sqrt.of.Ge_1 h
  exact All.of.All.All_Imp.binary this h₁

lemma Algebra.LtSumS.of.All_Le.Any_Lt
  {n : ℕ}
  {x y : ℕ → ℝ}
  (h₀ : ∀ i ∈ range n, x i ≤ y i)
  (h₁ : ∃ i ∈ range n, x i < y i) :
  ∑ i ∈ range n, x i < ∑ i ∈ range n, y i := by
  let ⟨i', h⟩ := h₁
  let ⟨h_In, h_Lt⟩ := h
  let y' := fun i => ite (i = i') (x i) (y i)
  have h_y' : ∀ i ∈ range n, y' i = ite (i = i') (x i) (y i) := by
    intro i hj
    by_cases h : i = i'
    ·
      rw [h]
    ·
      unfold y'
      simp [h]
  have := All_Le.of.All_Le.All_Eq_Ite h_In h₀ h_y'
  have h_Le := LeSumS.of.All_Le this
  have := Sum.eq.Sum_Add_Sub.of.Mem_Range.All_Eq_Ite h_In h_y'
  have h_Lt_0 := Sub.lt.Zero.of.Lt h_Lt
  have := Lt.of.Eq_Add.Lt_0 this h_Lt_0
  exact Lt.of.Le.Lt h_Le this

lemma Algebra.Lt.of.Lt.Le
  [Preorder α]
  {a b c : α}
  (h₀ : a < b)
  (h₁ : b ≤ c) :
  a < c :=
  lt_of_lt_of_le h₀ h₁

lemma Set.Lt.ou.Eq.of.Mem_Range
  {n i : ℕ}
  (h : i ∈ Finset.range (n + 1)) :
  i < n ∨ i = n := by
  apply Lt.ou.Eq.of.Le
  apply Le.of.Lt_Add_1
  apply Lt.of.Mem_Range h

lemma Logic.All_Not.of.NotAny.finset
  {f : ι → Prop}
  {s : Finset ι}
  (h : ¬∃ i ∈ s, f i) :
  ∀ i ∈ s, ¬(f i) := by
  -- Use classical reasoning to handle the negation and existence
  classical
  -- Apply the principle of excluded middle to derive the existence of an element not satisfying f
  by_contra! h'
  -- Obtain a contradiction by combining the original hypothesis with the derived universal statement
  exact h h'

lemma Logic.All_Not.of.NotAny
  {p : α → Prop}
  (h : ¬∃ x : α, p x) :
  ∀ x : α, ¬p x := by
  push_neg at h
  exact h

lemma Logic.All_And.of.All.All
  {f g : ι → Prop}
  {s : Finset ι}
  (h₀ : ∀ i ∈ s, f i)
  (h₁ : ∀ i ∈ s, g i) :
  ∀ i ∈ s, f i ∧ g i := by
  intro i hi
  -- Introduce the universal quantifier and set membership
  apply And.intro
  -- Split the goal into proving f i and g i separately
  -- Apply the first hypothesis h₀ to get f i
  exact h₀ i hi
  -- Apply the second hypothesis h₁ to get g i
  exact h₁ i hi

lemma Algebra.Gt.of.Ge.Gt
  [Preorder α]
  {a b c : α}
  (h₀ : a ≥ b)
  (h₁ : b > c) :
  a > c :=
  gt_of_ge_of_gt h₀ h₁

lemma Algebra.SubAddSqrt.lt.Mul_SqrtDiv.of.Gt_1.Gt_1
  {n : ℕ}
  {x : ℝ}
  (h₀ : n > 1)
  (h₁ : x > 1) :
  √x + n - 1 < n * √((x + n - 1) / n) := by
  apply Lt.of.LtSquareS.Ge_0
  ·
    rw [SquareMul.eq.MulSquareS]
    rw [EqSquareSqrt.of.Ge_0]
    ·
      rw [SubAdd.eq.Add_Sub]
      rw [SquareAdd.eq.AddAddSquareS_MulMul2]
      field_simp
      rw [DivMul.eq.MulDiv]
      rw [EqDivSquare]
      rw [SubAdd.eq.Add_Sub]
      rw [Mul_Add.eq.AddMulS]
      apply Lt.of.Sub.gt.Zero
      rw [SubAdd.eq.AddSub]
      rw [Sub_Add.eq.SubSub]
      rw [Sub_Add.eq.SubSub]
      rw [SubMul.eq.MulSub_1]
      rw [SubSub.comm]
      rw [AddSub.eq.Add_Sub]
      rw [Square.eq.Mul]
      rw [SubMulS.eq.MulSub]
      rw [EqSub_Sub]
      rw [Mul.comm]
      rw [SubMulS.eq.MulSub]
      rw [AddMulS.eq.MulAdd]
      apply Mul.gt.Zero.of.Gt_0.Gt_0
      ·
        apply AddSub_Mul2Sqrt.gt.Zero.of.Gt_1 h₁
      ·
        simp
        linarith [h₀]
    ·
      apply Div.ge.Zero.of.Ge_0.Gt_0
      ·
        linarith [h₀]
      ·
        norm_cast
        linarith [h₀]
  ·
    apply Mul.ge.Zero.of.Ge_0.Ge_0
    ·
      simp
    ·
      apply Sqrt.ge.Zero

lemma Algebra.Sum.eq.Add_Sum.of.Gt_0
  {n : ℕ}
  {x : ℕ → ℝ}
  (h : n > 0) :
  ∑ i ∈ range n, x i = x 0 + ∑ i ∈ Finset.Ico 1 n, x i := by
  -- Split the sum into the first term and the rest
  let n' := n - 1
  have h_n' : n' = n - 1 := rfl
  have h_n : n = n' + 1 := by
    simp [h_n']
    simp [EqAddSub.of.Le (by linarith [h] : 1 ≤ n)]
  rw [h_n]
  rw [Finset.sum_range_succ']
  rw [Add.comm]
  apply EqAddS.of.Eq.left
  rw [Finset.sum_Ico_eq_sum_range]
  simp [EqSubAdd.int]
  simp [Add.comm]

lemma Logic.And_And.is.AndAnd :
  p ∧ q ∧ r ↔ (p ∧ q) ∧ r :=
  AndAnd.is.And_And.symm

lemma Algebra.AllIco.of.AllRange
  {n : ℕ}
  {p : ℕ → Prop}
  (h₀ : ∀ i ∈ range n, p i)
  (a : ℕ) :
  ∀ i ∈ Finset.Ico a n, p i := by
  intro i hi
  have h_Lt : i < n := by
    -- Extract the upper bound from the interval membership
    rw [Finset.mem_Ico] at hi
    linarith
  have h_In : i ∈ range n := by
    simp [h_Lt]
  exact h₀ i h_In

lemma Algebra.SubNatNat.eq.Sub
  {a b : ℕ} :
  Int.subNatNat a b = (a - b : ℤ) := by
  apply Int.subNatNat_eq_coe

lemma Algebra.Pow1.eq.One
  {x : ℝ} :
  (1 : ℝ) ^ x = 1 := by
  simp

lemma Set.Mem_Range.of.Lt
  {i n : ℕ}
  (h : i < n) :
  i ∈ Finset.range n := by
  -- Apply the lemma that connects membership in Finset.range n with the inequality i < n.
  rw [Finset.mem_range]
  -- Use the given hypothesis h : i < n to conclude the proof.
  exact h

/--
Given a non-zero natural number `n` and a sequence `x` of real numbers where each element is at least 1, if the average of the first `n` elements equals the `n`-th element, then the sum of the square roots of the first `n` elements is bounded above by `n` times the square root of the `n`-th element.
This result leverages the Cauchy-Schwarz inequality and algebraic manipulations under the specified conditions.
-/
lemma Algebra.Sum_Sqrt.le.Mul_Sqrt.of.EqDivSum.All_Ge_1.Ne_0
  {n : ℕ}
  {x : ℕ → ℝ}
  (h₀ : n ≠ 0)
  (h₁ : ∀ i ∈ range n, x i ≥ 1)
  (h₂ : (∑ i ∈ range n, x i) / n = x n) :
  (∑ i ∈ range n, √(x i)) ≤ n * √(x n) := by
  have : ∀ t : ℝ, t ≥ 1 → t ≥ 0 := by
    intro t h
    linarith
  have h_Ge_0 := All.of.All.All_Imp this h₁
  have h_Le := Sum_Sqrt.le.SqrtMul_Sum.of.All_Ge_0.cauchy_schwarz h_Ge_0
  have h_Eq := EqMulS.of.Eq h₂ n
  rw [EqMulDiv.of.Ne_0 (by simp [h₀] : (n : ℝ) ≠ 0)] at h_Eq
  rw [h_Eq] at h_Le
  rw [Mul_Mul.comm] at h_Le
  rw [Mul.eq.Square] at h_Le
  rw [Mul.comm] at h_Le
  have := Sum.ge.Zero.of.All_Ge_0 h_Ge_0
  have h_n : (n : ℝ) > 0 := by
    simp
    apply Gt_0.of.Ne_0 h₀
  have := GeDivS.of.Ge.Gt_0 this h_n
  norm_num at this
  rw [h_Eq] at this
  rw [EqDivMul.of.Ne_0 (by simp [h₀] : (n : ℝ) ≠ 0)] at this
  have := EqSquareSqrt.of.Ge_0 this
  rw [← this] at h_Le
  rw [SqrtMulSquareS.eq.Mul.of.Ge_0.Ge_0 (by norm_num) (by apply Sqrt.ge.Zero)] at h_Le
  assumption

lemma Logic.NotAny_Not.of.All.finset
  {f : ι → Prop}
  {s : Finset ι}
  (h : ∀ i ∈ s, f i) :
  ¬∃ i ∈ s, ¬(f i) := by
  -- Use classical reasoning to handle the negation and existence
  classical
  -- Apply the principle of excluded middle to derive the existence of an element not satisfying f
  by_contra! h'
  -- Obtain a contradiction by combining the original hypothesis with the derived universal statement
  let ⟨i, hi, hni⟩ := h'
  exact absurd (h i hi) hni

lemma Logic.NotAny_Not.of.All
  {p : α → Prop}
  (h : ∀ x : α, p x) :
  ¬∃ x : α, ¬p x := by
  push_neg
  exact h

lemma Algebra.CoeSub.eq.SubCoeS.of.Ge
  [AddGroupWithOne α]
  {a b : ℕ}
  (h : a ≥ b) :
  ((a - b : ℕ) : α) = a - b :=
  Nat.cast_sub h

lemma Algebra.Root_Add_2.lt.Sqrt.of.Gt_1.Gt_0
  {x : ℝ}
  {i : ℕ}
  (h : x > 1)
  (h₁ : i > 0) :
  x ^ (1 / (i + 2) : ℝ) < √x := by
  -- We need to show that x^(1/(i+2)) ≤ x^(1/2) for x ≥ 1 and i a natural number.
  -- First, note that i + 2 ≥ 3 since i is a natural number.
  -- Therefore, 1/(i+2) ≤ 1/3 < 1/2.
  -- For x ≥ 1, the function f(k) = x^k is increasing.
  -- Hence, x^(1/(i+2)) ≤ x^(1/2).
  rw [Sqrt.eq.Root_2]
  -- Use the property that for x ≥ 1, the function x^k is increasing.
  -- This allows us to compare the exponents directly.
  apply Real.rpow_lt_rpow_of_exponent_lt h
  -- Show that 1/(i+2) ≤ 1/2 for all natural numbers i.
  rw [div_lt_div_iff₀]
  ·
    norm_num
    assumption
  ·
    linarith
  ·
    norm_num

lemma Algebra.CoeSub.eq.SubCoeS.rat
  [DivisionRing α]
  [CharZero α]
  {a b : ℚ} :
  ↑(a - b) = (a - b : α) :=
  Rat.cast_sub a b

lemma Algebra.CoeSub.eq.SubCoeS
  [AddGroupWithOne α]
  {a b : ℤ} :
  ((a - b : ℤ) : α) = a - b :=
  Int.cast_sub a b

lemma Algebra.Any_Gt.of.All_Ge.Any_Ne
  {n : ℕ}
  {a : ℝ}
  {x : ℕ → ℝ}
  (h₁ : ∀ i ∈ range n, x i ≥ a)
  (h₂ : ∃ i ∈ range n, x i ≠ a) :
  ∃ i ∈ range n, x i > a := by
  by_contra h
  have h := All_Not.of.NotAny.finset h
  have : ∀ t : ℝ, ¬t > a → t ≤ a := by
    intro t h
    linarith
  have h_Ge_0 := All.of.All.All_Imp (α := ℝ) this h
  have h := All_And.of.All.All h₁ h_Ge_0
  have : ∀ t : ℝ, t ≥ a ∧ t ≤ a → t = a := by
    intro t h
    linarith
  have h := All.of.All.All_Imp this h
  have := NotAny_Not.of.All h
  have h_NotAny : ¬∃ i ∈ range n, x i ≠ a := by
    simp [this]
    simp at h
    exact h
  contradiction

lemma Set.Mem_Range.ou.Eq.of.Mem_Range
  {n i : ℕ}
  (h : i ∈ Finset.range (n + 1)) :
  i ∈ Finset.range n ∨ i = n := by
  have := Lt.ou.Eq.of.Mem_Range h
  cases' this with h_Lt h_Eq
  ·
    exact Or.inl (Mem_Range.of.Lt h_Lt)
  ·
    exact Or.inr h_Eq

/--
Given a natural number `n > 1` and a sequence `x` of real numbers indexed by natural numbers, this lemma establishes an inequality involving sums of roots under the following conditions:
1. Each element `x i` for `i` in the range `[0, n-1]` is at least 1.
2. The first element `x 0` is strictly greater than 1.
3. The average of the first `n` elements of `x` equals the `n`-th element `x n`.
Under these conditions, the sum of each `x i` raised to the power `1/(i+2)` for `i` from 0 to `n-1` is strictly less than `n` times the square root of `x n`.
-/
lemma Algebra.Sum_Root.lt.Mul_Sqrt.of.EqDivSum.All_Ge_1.Gt_1.Gt_1
  {n : ℕ}
  {x : ℕ → ℝ}
  (h₀ : n > 1)
  (h₁ : ∀ i ∈ range n, x i ≥ 1)
  (h₂ : x 0 > 1)
  (h₃ : (∑ i ∈ range n, x i) / n = x n) :
  ∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) < n * √(x n) := by
  have h_All := All_LeRoot_Sqrt.of.All_Ge_1 h₁
  by_cases h : ∃ i ∈ Finset.Ico 1 n, x i > 1
  ·
    let ⟨i, hi⟩ := h
    let ⟨h_In, h_Gt_1⟩ := hi
    rw [Finset.mem_Ico] at h_In
    have h_Gt_0 := Gt.of.Ge.Gt h_In.left (by norm_num : 1 > 0)
    have h := Root_Add_2.lt.Sqrt.of.Gt_1.Gt_0 h_Gt_1 h_Gt_0
    have h_Any : ∃ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) < √(x i) := by
      use i
      constructor
      ·
        rw [Finset.mem_range]
        exact h_In.right
      ·
        assumption
    have h_Lt := LtSumS.of.All_Le.Any_Lt h_All h_Any
    have := Sum_Sqrt.le.Mul_Sqrt.of.EqDivSum.All_Ge_1.Ne_0 (by linarith [h₀]) h₁ h₃
    exact Lt.of.Lt.Le h_Lt this
  ·
    have := All_Not.of.NotAny h
    simp [And_And.is.AndAnd] at this
    have h_All_Le_1 : ∀ i ∈ Finset.Ico 1 n, x i ≤ 1 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact this i hi.left hi.right
    have h_All_Ge_1 := AllIco.of.AllRange h₁ 1
    have h_All_And := All_And.of.All.All h_All_Le_1 h_All_Ge_1
    have : ∀ t : ℝ, t ≤ 1 ∧ t ≥ 1 → t = 1 := by
      intro t ht
      exact Eq.of.Le.Ge ht.left ht.right
    have h_All_Eq := All.of.All.All_Imp this h_All_And
    let f := fun (xi : ℝ) (i : ℕ) => xi ^ (1 / (i + 2) : ℝ)
    have h_All_Eq_Root := All_EqFunS.of.All_Eq.binary (f := f) h_All_Eq
    simp only [f] at h_All_Eq_Root
    let f := fun i : ℕ => (x i) ^ (1 / (i + 2) : ℝ)
    have h_Eq_Sum := Sum.eq.Add_Sum.of.Gt_0 (x := f) (by linarith [h₀])
    simp only [f] at h_Eq_Sum
    simp only [EqAdd0.nat (R := ℝ)] at h_Eq_Sum
    rw [Root_2.eq.Sqrt] at h_Eq_Sum
    have h_Eq_Sum' := EqSumS.of.All_Eq h_All_Eq_Root
    simp only [Pow1.eq.One] at h_Eq_Sum'
    have h_Eq_Sub : ∑ x ∈ Finset.Ico 1 n, (1 : ℝ) = n - 1 := by
      norm_cast
      simp
      rw [SubNatNat.eq.Sub]
      rw [CoeSub.eq.SubCoeS.of.Ge (by linarith [h₀])]
    have h_Eq_Sum' := Eq.trans h_Eq_Sum' h_Eq_Sub
    rw [h_Eq_Sum'] at h_Eq_Sum
    norm_cast at h_Eq_Sum
    rw [SubNatNat.eq.Sub] at h_Eq_Sum
    rw [CoeSub.eq.SubCoeS] at h_Eq_Sum
    simp only [Add_Sub.eq.SubAdd] at h_Eq_Sum
    norm_cast
    norm_cast at h_Eq_Sum
    rw [h_Eq_Sum]
    have h_Eq_Sum_1 := EqSumS.of.All_Eq h_All_Eq
    have h_Eq_Sum := Sum.eq.Add_Sum.of.Gt_0 (x := x) (by linarith [h₀])
    rw [h_Eq_Sum_1] at h_Eq_Sum
    rw [h_Eq_Sub] at h_Eq_Sum
    rw [Add_Sub.eq.SubAdd] at h_Eq_Sum
    rw [h_Eq_Sum] at h₃
    rw [← h₃]
    apply SubAddSqrt.lt.Mul_SqrtDiv.of.Gt_1.Gt_1
    assumption
    assumption

lemma Algebra.All_Eq.of.All_Eq.Eq
  {x y : ℕ → α}
  (h₀ : x n = y n)
  (h₁ : ∀ i ∈ range n, x i = y i) :
  ∀ i ∈ range (n + 1), x i = y i := by
  -- Introduce the index `i` and the hypothesis `hi` that `i` is in the range `n + 1`.
  intro i hi
  -- Perform case analysis on the hypothesis `hi` to split into two cases: `i < n` and `i = n`.
  cases' Mem_Range.ou.Eq.of.Mem_Range hi with h h
  ·
    -- Case 1: `i < n`. Use the hypothesis `h₁` which states `x i = y i` for all `i` in the range `n`.
    simp_all [h₁]
  ·
    -- Case 2: `i = n`. Use the hypothesis `h₀` which states `x n = y n`.
    simp_all [h₀]

/--
Given a sequence \( \{x_i\}_{i=0}^{n-1} \) with \( n > 1 \), where each \( x_i \geq 1 \) and at least one \( x_i \neq 1 \), and the average \( \frac{1}{n}\sum_{i=0}^{n-1} x_i = x_n \), this lemma establishes that the sum of the terms raised to the power \( \frac{1}{i+2} \) is strictly less than \( n \times \sqrt{x_n} \).
The proof leverages inequalities between roots and the Cauchy-Schwarz inequality, ensuring the strictness due to the presence of elements greater than 1.
-/
lemma Algebra.Sum_Root.lt.Mul_Sqrt.of.EqDivSum.Any_Ne_1.All_Ge_1.Gt_1
  {n : ℕ}
  {x : ℕ → ℝ}
  (h₀ : n > 1)
  (h₁ : ∀ i ∈ range n, x i ≥ 1)
  (h₂ : ∃ i ∈ range n, x i ≠ 1)
  (h₃ : (∑ i ∈ range n, x i) / n = x n) :
  ∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) < n * √(x n) := by
  have := Any_Gt.of.All_Ge.Any_Ne h₁ h₂
  let ⟨i, h⟩ := this
  let ⟨h_In, h_Gt⟩ := h
  have := Lt.of.Mem_Range h_In
  have h_n : n > 0 := by
    linarith [this]
  by_cases h : i = 0
  ·
    rw [h] at h_Gt
    exact Sum_Root.lt.Mul_Sqrt.of.EqDivSum.All_Ge_1.Gt_1.Gt_1 h₀ h₁ h_Gt h₃
  ·
    have h_All := All_LeRoot_Sqrt.of.All_Ge_1 h₁
    have h := Gt_0.of.Ne_0 h
    have h := Root_Add_2.lt.Sqrt.of.Gt_1.Gt_0 h_Gt h
    have h_Any : ∃ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) < √(x i) := by
      use i
    have h_Lt := LtSumS.of.All_Le.Any_Lt h_All h_Any
    have := Sum_Sqrt.le.Mul_Sqrt.of.EqDivSum.All_Ge_1.Ne_0 (by linarith [h₀]) h₁ h₃
    exact Lt.of.Lt.Le h_Lt this

lemma Algebra.Sum.eq.SMulCard.of.All_Eq
  [AddCommMonoid α]
  {s : Finset ι}
  {x : ι → α}
  {a : α}
  (h : ∀ i ∈ s, x i = a) :
  ∑ i ∈ s, x i = s.card • a := by
  let y := fun _ : ι => a
  have := EqSumS.of.All_Eq (y := y) h
  simp [y] at this
  assumption

lemma Algebra.Eq.of.All_Eq.Lt
  {x y : ℕ → α}
  (h₀ : m < n)
  (h₁ : ∀ i ∈ range n, x i = y i) :
  x m = y m := by
  -- Apply the universal statement `h₁` to the specific index `m`
  apply h₁ m
  -- Provide the proof that `m < n` (from `h₀`) to satisfy the membership in `range n`
  apply Mem_Range.of.Lt h₀

lemma Algebra.Div.eq.One.of.Ne_0
  [GroupWithZero α]
  {a : α}
  (h : a ≠ 0) :
  a / a = 1 := by
  simp [h]

lemma Logic.Any_Not.of.NotAll.finset
  {f : ι → Prop}
  {s : Finset ι}
  (h : ¬∀ i ∈ s, f i) :
  ∃ i ∈ s, ¬(f i) := by
  -- Use classical reasoning to handle the negation and existence
  classical
  -- Apply the principle of excluded middle to derive the existence of an element not satisfying f
  by_contra! h'
  -- Obtain a contradiction by combining the original hypothesis with the derived universal statement
  exact h (fun i hi => by simpa using h' i hi)

lemma Logic.Any_Not.of.NotAll
  {p : α → Prop}
  (h : ¬∀ x : α, p x) :
  ∃ x : α, ¬p x := by
  push_neg at h
  exact h

lemma Algebra.LtCoeS.of.Lt.nat
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ}
  (h : a < b) :
  (a : R) < (b : R) := by
  apply Nat.cast_lt.mpr h

lemma Algebra.LtCoeS.of.Lt.int
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
  {a b : ℤ}
  (h : a < b) :
  (a : R) < (b : R) := by
  apply Int.cast_lt.mpr h

lemma Algebra.LtCoeS.of.Lt
  [LinearOrderedField R]
  {a b : ℚ}
  (h : a < b) :
  (a : R) < (b : R) := by
  apply Rat.cast_lt.mpr h

lemma Algebra.All_Eq.of.All_Eq.Lt
  {x y : ℕ → α}
  (h₀ : m < n)
  (h₁ : ∀ i ∈ range n, x i = y i) :
  ∀ i ∈ range m, x i = y i := by
  -- Introduce an arbitrary element `i` in the range up to `m`
  intro i hi
  -- Simplify the membership condition `hi` to `i < m`
  simp at hi
  -- Use linear arithmetic to prove `i < n` from `i < m` and `m < n`
  have hi' : i < n := by linarith [h₀, hi]
  -- Apply the universal equality hypothesis `h₁` to `i` and the proof `i < n`
  have h_Mem := Mem_Range.of.Lt hi'
  exact h₁ i h_Mem

lemma Algebra.Div.eq.One.of.Gt_0
  [Preorder α]
  [GroupWithZero α]
  {x : α}
  (h : x > 0) :
  x / x = 1 :=
  (Div.eq.One.of.Ne_0 ∘ Ne.of.Gt) h

lemma Algebra.All_Eq.of.All_Eq.Lt.is_constant
  {x : ℕ → α}
  {a : α}
  (h₀ : m < n)
  (h₁ : ∀ i ∈ range n, x i = a) :
  ∀ i ∈ range m, x i = a := by
  let y := fun _ : ℕ => a
  have := All_Eq.of.All_Eq.Lt (y := y) h₀ h₁
  simp only [y] at this
  assumption

lemma Algebra.Eq.of.All_Eq.Lt.is_constant
  {x : ℕ → α}
  (h₀ : m < n)
  (h₁ : ∀ i ∈ range n, x i = a) :
  x m = a := by
  let y := fun _ : ℕ => a
  have := Eq.of.All_Eq.Lt (y := y) h₀ h₁
  simp only [y] at this
  assumption

lemma Algebra.Gt.of.Gt.Gt
  [Preorder α]
  {a b c : α}
  (h₀ : a > b)
  (h₁ : b > c) :
  a > c :=
  gt_trans h₀ h₁

lemma Algebra.All_Eq.of.All_Eq.Eq.is_constant
  {x : ℕ → α}
  {a : α}
  (h₀ : x n = a)
  (h₁ : ∀ i ∈ range n, x i = a) :
  ∀ i ∈ range (n + 1), x i = a := by
  let y := fun _ : ℕ => a
  have := All_Eq.of.All_Eq.Eq (y := y) h₀ h₁
  simp only [y] at this
  assumption

lemma Algebra.Sum.eq.Mul.of.All_Eq
  [Ring α]
  {x : ℕ → α}
  {a : α}
  {n : ℕ}
  (h : ∀ i ∈ range n, x i = a) :
  ∑ i ∈ range n, x i = n * a := by
  have := Sum.eq.SMulCard.of.All_Eq h
  simp at this
  assumption

/--
Given a natural number \( n > 1 \) and a sequence \( \{x_i\} \) where each \( x_i \geq 1 \), if the sum of \( x_i^{1/(i+2)} \) for \( i \) in the range \( 1 \) to \( n \) equals \( n \sqrt{x_n} \) and the average of \( \{x_i\} \) is \( x_n \), then all \( x_i \) must be equal to \( 1 \).
-/
lemma Algebra.All_Eq_1.of.All_Ge_1.Sum_Root.eq.Mul_Root_2.EqDivSum.Gt_1
  {n : ℕ}
  {x : ℕ → ℝ}
  (h₀ : n > 1)
  (h₁ : (∑ i ∈ range n, x i) / n = x n)
  (h₂ : (∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ)) = n * (x n) ^ (1 / 2 : ℝ))
  (h₃ : ∀ i ∈ range n, x i ≥ 1) :
  ∀ i ∈ range n, x i = 1 := by
  rw [Root_2.eq.Sqrt] at h₂
  by_contra h
  have h : ∃ i ∈ range n, ¬(x i = 1) := Any_Not.of.NotAll.finset h
  have := Sum_Root.lt.Mul_Sqrt.of.EqDivSum.Any_Ne_1.All_Ge_1.Gt_1 h₀ h₃ h h₁
  have := Ne.of.Lt this
  contradiction

lemma Algebra.GtCoeS.of.Gt.nat
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ}
  (h : a > b) :
  (a : R) > (b : R) :=
  LtCoeS.of.Lt.nat h

lemma Algebra.GtCoeS.of.Gt.int
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
  {a b : ℤ}
  (h : a > b) :
  (a : R) > (b : R) :=
  LtCoeS.of.Lt.int h

lemma Algebra.GtCoeS.of.Gt
  [LinearOrderedField R]
  {a b : ℚ}
  (h : a > b) :
  (a : R) > (b : R) :=
  LtCoeS.of.Lt h

lemma Algebra.Ge.of.Eq
  [Preorder α]
  {x y : α}
  (h : x = y) :
  x ≥ y := by
  rw [h]

/--
This lemma establishes that for a sequence of real numbers indexed by natural numbers, the conditions of having the average of the first `n` terms equal to the `n`-th term, the sum of their roots matching a specific form, and all terms being at least one, are equivalent to all terms up to `n + 1` being exactly one.
It provides a characterization of constant sequences under these constraints, useful in verifying uniqueness and optimality in related problems.
-/
theorem algebra_604669
  {n : ℕ}
  {x : ℕ → ℝ}
  (h : n > 1) :
  ((∑ i ∈ range n, x i) / n = x n ∧ (∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ)) = n * (x n) ^ (1 / 2 : ℝ) ∧ ∀ i ∈ range n, x i ≥ 1) ↔ ∀ i ∈ range (n + 1), x i = 1 := by
  have h_Gt_1 := GtCoeS.of.Gt.nat (R := ℝ) h
  have h_Gt_0 : (n : ℝ) > 0 := by apply Gt.of.Gt.Gt h_Gt_1 (by norm_num)
  constructor
  ·
    intro ⟨h₁, h₂, h₃⟩
    have h' := All_Eq_1.of.All_Ge_1.Sum_Root.eq.Mul_Root_2.EqDivSum.Gt_1 h h₁ h₂ h₃
    have := Sum.eq.Mul.of.All_Eq h'
    simp at this
    have := EqDivS.of.Eq this n
    simp [Div.eq.One.of.Gt_0 h_Gt_0] at this
    have h₁ := h₁.symm.trans this
    apply All_Eq.of.All_Eq.Eq.is_constant h₁ h'
  ·
    intro h'
    have h_Lt : n < n + 1 := by norm_num
    have h_All_Eq := All_Eq.of.All_Eq.Lt.is_constant h_Lt h'
    have h_Eq := Eq.of.All_Eq.Lt.is_constant h_Lt h'
    constructor
    ·
      have := Sum.eq.Mul.of.All_Eq h_All_Eq
      simp at this
      have := EqDivS.of.Eq this n
      simp [Div.eq.One.of.Gt_0 h_Gt_0] at this
      apply this.trans h_Eq.symm
    ·
      constructor
      ·
        rw [h_Eq]
        rw [Pow1.eq.One]
        let b := fun _ : ℕ => (1 : ℝ)
        let f := fun (x : ℝ) (i : ℕ) => x ^ (1 / (i + 2) : ℝ)
        have := All_EqFunS.of.All_Eq.binary (b := b) (f := f) h_All_Eq
        simp only [b, f] at this
        simp only [Pow1.eq.One] at this
        apply Sum.eq.Mul.of.All_Eq this
      ·
        have h_All : ∀ x : ℝ, x = 1 → x ≥ 1 := by
          intro i h_Eq
          apply Ge.of.Eq h_Eq
        apply All.of.All.All_Imp h_All h_All_Eq
