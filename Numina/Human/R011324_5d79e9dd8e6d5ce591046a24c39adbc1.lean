import Mathlib

/- 25. (KOR 3) Let $a, b$ be integers that are not perfect squares. Prove that if  $$ x^{2}-a y^{2}-b z^{2}+a b w^{2}=0 $$  has a nontrivial solution in integers, then so does  $$ x^{2}-a y^{2}-b z^{2}=0 $$ -/
theorem number_theory_24231 (a b : ℤ) (ha : ¬ ∃ m, m ^ 2 = a) (hb : ¬ ∃ n, n ^ 2 = b) (h: ∃ x y z w : ℤ,  (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0)∧(x^2 - a * y^2 - b * z^2 + a * b * w^2 = 0)) :
  ∃ x' y' z' : ℤ, (x' ≠ 0 ∨ y' ≠ 0 ∨ z' ≠ 0) ∧ (x'^2 - a * y'^2 - b * z'^2 = 0) := by

  --We will show that the following value works.
  obtain ⟨x,y,z,w,hn,h⟩ := h
  use (x*z - a *y*w)
  use (y*z-x*w)
  use (z^2-a*w^2)

  constructor

  --We need to prove that not all of these three values equal 0. Suppose on the contrary.
  by_contra alleq0
  push_neg at alleq0
  obtain ⟨xp,yp,zp⟩ := alleq0

  --We will have w = 0, since otherwise a = (z/w)^2 is a square.
  have we : w = 0 := by 
    by_contra wne0
    have : w^2 * a = z^2 := by linarith
    have w2dz2: w^2 ∣ z^2 := by use a; linarith only [this]
    have wdz : w ∣ z := by rw [Int.pow_dvd_pow_iff] at w2dz2; exact w2dz2; norm_num
    obtain ⟨k,hk⟩ := wdz
    have : k^2 = a := by 
      have : w^2 * a = w^2 * k^2 := by simp [hk] at this; rw [this]; ring
      have : w^2 * (a-k^2) = 0 := by linarith
      simp [wne0] at this
      linarith
    push_neg at ha
    specialize ha k
    contradiction

  have ze : z = 0 := by 
    simp [we] at zp;
    exact zp

  --We put w = 0 and z = 0 back to the orininal equation. By the same logic, we have y = 0 and then x = 0, which is a contradiction.
  simp [we,ze] at h
  have ye : y = 0 := by 
    by_contra yne0
    have : y^2 * a = x^2 := by linarith
    have y2dx2 : y^2 ∣ x^2 := by use a; linarith only [this]
    have ydx : y ∣ x := by rw [Int.pow_dvd_pow_iff] at y2dx2; exact y2dx2; norm_num
    obtain ⟨k,hk⟩ := ydx
    have : k^2 = a := by
      have : y^2 * a = y^2 * k^2 := by simp [hk] at this; rw [this]; ring
      have : y^2 * (a-k^2) = 0 := by linarith
      simp [yne0] at this
      linarith
    push_neg at ha
    specialize ha k
    contradiction

  have xe : x = 0 := by 
    simp [ye] at h
    exact h
  
  
  simp [xe,ye,ze,we] at hn


  --The remaining part is to check that the equation is valid. This is simple calculation using the given equation.
  have t1 : x^2 - a * y^2 = b * (z^2 - a * w^2) := by linarith
  have t2 : (x^2 - a * y^2) * (z^2 - a * w^2) - b * (z^2 - a * w^2)^2 = 0 := by nth_rw 5 [pow_two]; simp [t1]; ring
  nlinarith