import Mathlib

/-For a quadratic trinomial f(x) and some real numbers l,t and v
v, the following equalities are satisfied:
f(l)=t+v,f(t) =l+v,f(v)=l+t.
Prove that among the numbers l, t and v
there are equal numbers.-/

theorem algebra_185698 {l t v a b: ℝ} (ha: a ≠ 0) (f: ℝ → ℝ) (hf: ∀ x, f x = a * x ^ 2 + b * x + c)
(h1: f l = t + v) (h2: f t = l + v) (h3: f v = l + t):
    l = t ∨ t = v ∨ v = l := by

    by_contra! h
    rcases h with ⟨n1, n2, n3⟩
    simp [hf] at h1 h2 h3
    have r1: (l - t) * (a * (l + t) + b + 1) = 0 := by
        nlinarith
    have r2: (t - v) * (a * (t + v) + b + 1) = 0 := by
        nlinarith
    have r3: (v - l) * (a * (v + l) + b + 1) = 0 := by
        nlinarith
    clear h1 h2 h3
    replace n1: l - t ≠ 0 := by
        by_contra! o
        replace o: l = t := by
            nlinarith
        simp [o] at n1
    replace n2: t - v ≠ 0 := by
        by_contra! o
        replace o: t = v := by
            nlinarith
        simp [o] at n2
    replace n3: v - l ≠ 0 := by
        by_contra! o
        replace o: v = l := by
            nlinarith
        simp [o] at n3
    simp [n1, n2, n3] at r1 r2 r3
    have g1: a * (l + t) = a * (t + v) := by linarith
    simp [ha] at g1
    replace g1: l = v := by linarith
    simp [g1] at n3
    