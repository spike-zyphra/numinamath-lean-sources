import Mathlib
open Real

/-
Determine the positive real value of $x$ for which

$$
\sqrt{2+A C+2 C x}+\sqrt{A C-2+2 A x}=\sqrt{2(A+C) x+2 A C} .
$$
-/
theorem algebra_608928 (A C x: ℝ) (ha: A > 0) (hc: C> 0) (hx: x> 0) (hp: A*C - 2 + 2*A*x ≥ 0) (h: sqrt (2 + A*C + 2*C*x) + sqrt (A*C - 2 + 2*A*x)  = sqrt (2*(A+C)*x + 2*A*C)) : x = (2-A*C)/(2*A):= by

  -- A lemma to prove that if sqrt a + sqrt b = sqrt (a+b), then a=0 or b=0.
  have lemma1 {a b : ℝ} (ha: a≥ 0) (hb: b≥ 0) (h: sqrt a + sqrt b = sqrt (a+b)): a=0 ∨ b=0 := by
    have : a + b + 2 * sqrt a * sqrt b = a + b := by
      calc
        _ = (sqrt a + sqrt b)^2 := by
          ring_nf; rw [sq_sqrt ha, sq_sqrt hb]; ring_nf
        _ = (sqrt (a+b))^2 := by rw [h]
        _ = a + b := by  rw [sq_sqrt (add_nonneg ha hb)]
    have : sqrt a * sqrt b = 0 := by linarith
    simp at this
    rcases this with h | h
    have _1 : a = 0 := by
      calc
        _ = (sqrt a)^2 := by rw [sq_sqrt ha]
        _ = 0  := by rw [h]; linarith
    tauto
    have _2 : b = 0 := by
      calc
        _ = (sqrt b)^2 := by rw [sq_sqrt hb]
        _ = 0  := by rw [h]; linarith
    tauto

  -- Observe that in this case, a = (2 + A*C + 2*C*x) and b =  (A*C - 2 + 2*A*x)
  have : (2*(A+C)*x + 2*A*C) = (2 + A*C + 2*C*x) + (A*C - 2 + 2*A*x) := by ring_nf

  rw [this] at h
  have hp1: (2 + A*C + 2*C*x) > 0 := by
    have ht1: (2 + A * C) > 0 := by
      have ha': A≥ 0 := by linarith
      have hc': C≥ 0 := by linarith
      have htt1: A * C ≥ 0 := mul_nonneg ha' hc'
      linarith
    have ht2: 2 + A * C + 2 * C * x > 0 := by
      calc
        _ > 2*C*x := by linarith
        _ ≥ 0 := by
          apply mul_nonneg <;>
          linarith
    linarith

  -- Change variable to simplify the equation.
  let u:ℝ := 2 + A * C + 2 * C * x
  let v:ℝ := A * C - 2 + 2 * A * x
  have up: u> 0 := by
    unfold u; exact hp1
  have vp: v≥ 0 := by
    unfold v; exact hp
  have w: sqrt u + sqrt v = sqrt (u+v) := by
    unfold u v
    exact h
  have lemma2: u = 0 ∨ v = 0 := by
    exact lemma1 (by linarith) hp w
  
  -- Use the logic to show v = 0, since u > 0
  have v0: v = 0 := by
    apply Or.resolve_left at lemma2
    have : ¬ u=0 := by linarith
    tauto
  
  -- Calculate the result.
  have hx1: x = (2 - A*C)/(2*A) := by
    have e: 0 = A*C - 2 + 2*A*x := by
      calc
        _ = v := by linarith
        _ = A*C - 2 + 2*A*x := by unfold v; ring_nf
    have : 2 - A*C = 2*A*x := by linarith
    rw [this]
    field_simp
  
  exact hx1



  