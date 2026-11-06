import Mathlib

theorem algebra_229115 (a b c d : ℤ) (h : ∀ m n : ℤ, ∃ x y : ℤ,
    a * x + b * y = m ∧ c * x + d * y = n) :
    a * d - b * c = 1 ∨ a * d - b * c = -1 := by
  have h1 := h 1 0
  rcases h1 with ⟨x1, y1, h1₁, h1₂⟩
  have h2 := h 0 1
  rcases h2 with ⟨x2, y2, h2₁, h2₂⟩
  -- Now we have four equations:
  -- 1. a * x1 + b * y1 = 1
  -- 2. c * x1 + d * y1 = 0
  -- 3. a * x2 + b * y2 = 0
  -- 4. c * x2 + d * y2 = 1
  -- These equations imply that the matrix (a b; c d) is invertible and its inverse is (x1 x2; y1 y2).
  -- Therefore, the determinant ad-bc must be ±1.
  -- To see this, note that:
  -- (a b; c d) * (x1 x2; y1 y2) = (1 0; 0 1)
  -- Taking the determinant of both sides:
  -- det(A)det(B) = det(I) = 1
  -- Using the property det(AB) = det(A)det(B):
  -- (ad-bc)(x1*y2 - x2*y1) = 1
  -- Since x1*y2 - x2*y1 is an integer, we have that ad-bc divides 1.
  -- The only integers dividing 1 are ±1. Therefore ad-bc = ±1.
  have eq5 : (a * d - b * c) * (x1 * y2 - x2 * y1) = 1 := by
    nlinarith [sq_nonneg (a * y1 - b * x1), sq_nonneg (c * y1 - d * x1),
      sq_nonneg (a * y2 - b * x2), sq_nonneg (c * y2 - d * x2)]
  have eq6 : (a * d - b * c) = 1 ∨ (a * d - b * c) = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact eq5
  exact_mod_cast eq6