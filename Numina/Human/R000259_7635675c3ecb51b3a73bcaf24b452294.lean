
import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all pairs of positive integers  $ (a, b)$  such that
 $$ab \equal{} gcd(a, b) \plus{} lcm(a, b)$$. -/
theorem number_theory_8735 :
  {(a, b) : ℕ × ℕ | 0 < a ∧ 0 < b ∧ a * b = Nat.gcd a b + Nat.lcm a b} = {(2, 2)} := by
    ext x; simp; constructor <;> intro h
    · have xd1 : x.1.gcd x.2 ∣ x.1 := Nat.gcd_dvd_left x.1 x.2
      have xd2 : x.1.gcd x.2 ∣ x.2 := Nat.gcd_dvd_right x.1 x.2
      obtain ⟨x1, h1⟩ := xd1
      obtain ⟨x2, h2⟩ := xd2
      -- Let \( d = \gcd(a, b) \). Then, we can write:
      -- \[
      -- a = d \cdot x \quad \text{and} \quad b = d \cdot y
      -- \]
      -- where \( \gcd(x, y) = 1 \).
      set d := x.1.gcd x.2 with hd
      have dne0 : d ≠ 0 := by simp [d]; refine gcd_ne_zero_left (Nat.ne_of_gt h.1)
      -- Express \( \operatorname{lcm}(a, b) \):
      -- \[
      -- \operatorname{lcm}(a, b) = d \cdot x \cdot y
      -- \]
      have h3 : x.1.lcm x.2 = d * x1 * x2 := by
        have := Nat.gcd_mul_lcm x.1 x.2
        nth_rw 3 [h1, h2] at this
        simp [←hd, mul_assoc, dne0] at this
        linarith
      -- Substitute into the original equation:
      -- \[
      -- ab = d^2 \cdot x \cdot y
      -- \]
      -- \[
      -- \gcd(a, b) + \operatorname{lcm}(a, b) = d + d \cdot x \cdot y
      -- \]
      -- Setting them equal:
      -- \[
      -- d^2 \cdot x \cdot y = d + d \cdot x \cdot y
      -- \]
      -- Dividing both sides by \( d \) (since \( d \geq 1 \)):
      -- \[
      -- d \cdot x \cdot y = 1 + x \cdot y
      -- \]
      -- Rearranging:
      -- \[
      -- (d - 1) \cdot x \cdot y = 1
      -- \]
      rw [h3, h1, h2] at h
      have : (d - 1) * x1 * x2 = 1 := by
        have := h.2.2
        nth_rw 3 [←mul_one d] at this
        rw [mul_assoc d x1 x2, ←mul_add, mul_assoc] at this
        have := Nat.eq_of_mul_eq_mul_left (by omega) this
        nth_rw 2 [←one_mul x1] at this
        rw [←mul_assoc, mul_comm x1 d, mul_assoc, mul_assoc] at this
        rw [mul_assoc, Nat.sub_mul]
        apply Nat.sub_eq_of_eq_add this
      rw [mul_assoc] at this
      --  Since \( d, x, y \) are positive integers and \( \gcd(x, y) = 1 \), the only possibility is:
      -- \[
      -- d - 1 = 1 \quad \text{and} \quad x \cdot y = 1
      -- \]
      -- This gives:
      -- \[
      -- d = 2 \quad \text{and} \quad x = y = 1
      -- \]
      -- Therefore:
      -- \[
      -- a = 2 \cdot 1 = 2 \quad \text{and} \quad b = 2 \cdot 1 = 2
      -- \]
      have d2 : d = 2 := by
        have :=  eq_one_of_mul_eq_one_right this
        omega
      have : x1 = 1 ∧ x2 = 1:= by
        have : x1 * x2 = 1 := eq_one_of_mul_eq_one_left this
        exact ⟨eq_one_of_mul_eq_one_right this, eq_one_of_mul_eq_one_left this⟩
      simp [d2, this] at h1 h2
      ext <;> simp [h1, h2]
    · -- Verification:**
      -- \[
      -- ab = 2 \times 2 = 4
      -- \]
      -- \[
      -- \gcd(2, 2) + \operatorname{lcm}(2, 2) = 2 + 2 = 4
      -- \]
      -- The equation holds true.
      simp [h]
