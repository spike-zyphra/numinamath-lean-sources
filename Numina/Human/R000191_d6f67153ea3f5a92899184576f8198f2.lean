import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Solve in integers the following equation: \[y=2x^2+5xy+3y^2\] -/
theorem number_theory_8522 : {(x, y) : ℤ × ℤ | y = 2 * x^2 + 5 * x * y + 3 * y^2} = {(-2, 1), (0, 0), (10, -8), (12, -9)} := by
ext ⟨x,y⟩; simp
constructor
-- main direction. given equations, decide x and y
intro eq0
have eq1: 2*(x*x)+5*y*x+(3*y^2-y) = 0 := by
  nth_rewrite 3 [eq0]
  ring
-- treat eq1 as a quadratic equation for x.
-- since x is integer, the discriminant must be perfect square.
have hy: ∃ k:ℤ, y^2 + 8*y = k^2 := by
  have h1: discrim 2 (5*y) (3*y^2-y) = (2*2*x+(5*y))^2 := by
    have eq1': 2 * (x * x) + 5 * y * x + (3 * y ^ 2 - y) = 0 := by
      rw [← eq1]
    apply discrim_eq_sq_of_quadratic_eq_zero eq1'
  have h2: discrim 2 (5*y) (3*y^2-y) = y^2 + 8*y := by
    simp [discrim]; ring
  rw [h2] at h1
  use (2*2*x+(5*y))
rcases hy with ⟨k,hk⟩
have eq2: (y+4+k)*(y+4-k) = 16 := by
  have ht1: y^2+8*y+16 = k^2+16 := by rw [hk]
  have ht2: y^2+8*y+16 = (y+4)^2 := by ring
  rw [ht2] at ht1
  have ht3: (y+4)^2-k^2 = 16 := Eq.symm (eq_sub_of_add_eq' (id (Eq.symm ht1)))
  have ht4: (y+4)^2-k^2 = (y+4+k)*(y+4-k) := _root_.sq_sub_sq (y + 4) k
  rwa [ht4] at ht3
-- since (y+4+k)*(y+4-k)=16, and they are integer, then they are factors of 16.
let fac1 := y+4+k
have hfac1: fac1 = y+4+k := rfl
let fac2 := y+4-k
have hfac2: fac2 = y+4-k := rfl
have eq2': fac1 * fac2 = 16 := eq2
have factors_16: ∀x:ℤ, 0 ≤ x → x ≤ 16 → x ∣ 16 → (x=1 ∨ x=2 ∨ x=4 ∨ x=8 ∨ x=16) := by decide
have facdvd: |fac1| ∣ 16 := by
  have: fac1 ∣ 16 := Dvd.intro (y+4-k) eq2
  exact (abs_dvd fac1 16).mpr this
have eqy: y=1 ∨ y=0 ∨ y=-9 ∨ y=-8 := by
  have h1: 0 ≤ |fac1| := abs_nonneg fac1
  have h16: (0:ℤ) ≤ 16 := by norm_num
  have h2: |fac1| ≤ 16 := by
    rcases facdvd with ⟨g,hg⟩
    by_cases ht: 1 ≤ g
    symm at hg
    have: |fac1| * g ≤ 16 := le_of_eq hg
    apply le_of_mul_le_of_one_le this h16 ht
    simp at ht
    have ht1: g ≤ 0 := Int.lt_add_one_iff.mp ht
    have ht2: 0 < |fac1| * g := by
      rw [← hg]; norm_num
    have ht3: |fac1| < 0 := neg_of_mul_pos_left ht2 ht1
    omega
  have h3: |fac1| = 1 ∨ |fac1| = 2 ∨ |fac1| = 4 ∨ |fac1| = 8 ∨ |fac1| = 16 := by
    apply factors_16 |fac1| h1 h2 facdvd
  -- given fac1, since fac1*fac2=16, we can determine fac2.
  -- since fac1=y+4+k and fac2=y+4-k, y and k are also determined.
  rcases h3 with hf1 | hf2 | hf4 | hf8 | hf16
  -- |fac1| = 1, 2, 4, 8, 16.  lots of work
  -- case |fac1| = 1
  have ht: fac1 = 1 ∨ fac1 = -1 := abs_eq_abs.mp hf1
  -- fac1 = 1
  rcases ht with ht1 | ht2
  rw [ht1] at eq2'
  have ht11: fac2 = 16 := by
    rw [← eq2']; ring
  rw [hfac1] at ht1
  rw [hfac2] at ht11
  have htt: y+4-k+1 = 16+1 := congrFun (congrArg HAdd.hAdd ht11) 1
  nth_rewrite 1 [← ht1] at htt
  simp at htt
  omega
  -- fac1 = -1
  rw [ht2] at eq2'
  have ht22: fac2 = -16 := by omega
  rw [hfac1] at ht2
  rw [hfac2] at ht22
  have htt: y+4-k+(-1) = -16 -1 := by omega
  nth_rewrite 1 [← ht2] at htt
  simp at htt
  omega
  -- case |fac1| = 2
  have ht: fac1 = 2 ∨ fac1 = -2 := abs_eq_abs.mp hf2
  rcases ht with ht1 | ht1
  rw [ht1] at eq2'
  have ht11: fac2 = 8 := by omega
  rw [hfac1] at ht1
  rw [hfac2] at ht11
  have htt: y+4-k+2 = 8+2 := by omega
  nth_rewrite 1 [← ht1] at htt
  simp at htt
  omega
  rw [ht1] at eq2'
  have ht11: fac2 = -8 := by omega
  rw [hfac1] at ht1
  rw [hfac2] at ht11
  have htt: y+4-k+(-2) = -8-2 := by omega
  nth_rewrite 1 [← ht1] at htt
  simp at htt
  omega
  -- case |fac1| = 4
  have ht: fac1 = 4 ∨ fac1 = -4 := abs_eq_abs.mp hf4
  rcases ht with ht1 | ht1
  rw [ht1] at eq2'
  have ht11: fac2 = 4 := by omega
  rw [hfac1] at ht1
  rw [hfac2] at ht11
  have htt: y+4-k+4 = 4+4 := by omega
  nth_rewrite 1 [← ht1] at htt
  simp at htt
  omega
  rw [ht1] at eq2'
  have ht11: fac2 = -4 := by omega
  rw [hfac1] at ht1
  rw [hfac2] at ht11
  have htt: y+4-k+(-4) = -4-4 := by omega
  nth_rewrite 1 [← ht1] at htt
  simp at htt
  omega
  -- case |fac1| = 8
  have ht: fac1 = 8 ∨ fac1 = -8 := abs_eq_abs.mp hf8
  rcases ht with ht1 | ht1
  rw [ht1] at eq2'
  have ht11: fac2 = 2 := by omega
  rw [hfac1] at ht1
  rw [hfac2] at ht11
  have htt: y+4-k+8 = 2+8 := by omega
  nth_rewrite 1 [← ht1] at htt
  simp at htt
  omega
  rw [ht1] at eq2'
  have ht11: fac2 = -2 := by omega
  rw [hfac1] at ht1
  rw [hfac2] at ht11
  have htt: y+4-k+(-8) = -2-8 := by omega
  nth_rewrite 1 [← ht1] at htt
  simp at htt
  omega
  -- case |fac1| = 16
  have ht: fac1 = 16 ∨ fac1 = -16 := abs_eq_abs.mp hf16
  rcases ht with ht1 | ht1
  rw [ht1] at eq2'
  have ht11: fac2 = 1 := by omega
  rw [hfac1] at ht1
  rw [hfac2] at ht11
  have htt: y+4-k+16 = 1+16 := by omega
  nth_rewrite 1 [← ht1] at htt
  simp at htt
  omega
  rw [ht1] at eq2'
  have ht11: fac2 = -1 := by omega
  rw [hfac1] at ht1
  rw [hfac2] at ht11
  have htt: y+4-k+(-16) = -1-16 := by omega
  nth_rewrite 1 [← ht1] at htt
  simp at htt
  omega
-- now, we have y=1, 0, -9, -8. calculate corresponding x
rcases eqy with eqy1 | eqy0 | eqy9 |eqy8
rw [eqy1] at eq1
simp at eq1
have: x = -2 := by
  have ht1: 2*(x*x)+5*x+2 = (x+2)*(2*x+1) := by ring
  rw [ht1] at eq1
  have ht2: x+2 = 0 ∨ 2*x+1 = 0 := Int.mul_eq_zero.mp eq1
  omega
left
exact ⟨this, eqy1⟩
rw [eqy0] at eq1
simp at eq1
right
left
exact ⟨eq1, eqy0⟩
rw [eqy9] at eq1
simp at eq1
have: x = 12 := by
  have ht1: 2*(x*x) + -(45*x) + 252 = (x-12)*(2*x-21) := by ring
  rw [ht1] at eq1
  have ht2: x-12 = 0 ∨ (2*x-21) = 0 := Int.mul_eq_zero.mp eq1
  omega
right
right
right
exact ⟨this, eqy9⟩
rw [eqy8] at eq1
simp at eq1
have: x = 10 := by
  have ht1: 2*(x*x) + -(40*x) + 200 = 2*(x-10)*(x-10) := by ring
  rw [ht1] at eq1
  simp at eq1
  omega
right
right
left
exact ⟨this, eqy8⟩
-- mpr direction. verify those (x,y) are corret solutions
intro h
rcases h with x2y1 | x0y0 | x10y8 | x12y9
rcases x2y1 with ⟨eqx2, eqy1⟩
rw [eqx2, eqy1]
simp
rcases x0y0 with ⟨eqx0, eqy0⟩
rw [eqx0, eqy0]
simp
rcases x10y8 with ⟨eqx10,eqy8⟩
rw [eqx10, eqy8]
simp
rcases x12y9 with ⟨eqx12, eqy9⟩
rw [eqx12, eqy9]
simp
