import Mathlib

/-
Let $(G, \cdot)$ be a multiplicative group with the identity element $e$ and
$x, y \in G$. Show that if $x^{2}=e$ and $x y x=y^{3}$, then $y^{8}=e$.
-/
theorem algebra_117137 {G : Type*} [Group G] (x y : G)
  (hxx : x^2 = 1)
  (hxyx : x * y * x = y^3) :
    y^8 = 1 := by
  -- Show y^9 = y by rearranging terms to fit hxx and hxyx
  have y_nine_eq_y : y^9 = y := calc
    _ = (y^3)^3 := npow_mul y 3 3
    -- Arrange in terms of y^3
    _ = y^3 * y^3 * y^3 := pow_three' _
    _ = (x * y * x) * (x * y * x) * (x * y * x) := by rw [hxyx]
    -- Arrange in terms of x^2
    _ = x * (y * (x * x) * y * (x * x) * y) * x := by simp only [mul_assoc]
    _ = x * (y * 1 * y * 1 * y) * x := by rw [<- pow_two, hxx, mul_one]
    _ = x * y^3 * x := by simp [pow_one, pow_three']
    -- Arrange in terms of x^2 again
    _ = x * (x * y * x) * x := by rw [← hxyx]
    _ = (x * x) * y * (x * x) := by simp only [mul_assoc]
    _ = 1 * y * 1 := by rw [<-pow_two, hxx]
    _ = y := by simp

  -- Cancel a factor of y on both sides
  rw [←pow_one y, show 9 = 8 + 1 by rfl, pow_add] at y_nine_eq_y
  simp_all