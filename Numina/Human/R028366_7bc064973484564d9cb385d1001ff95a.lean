import Mathlib

/-
  Let $\mathbb{Z}_{>0}$ be the set of positive integers. Find all functions $f: \mathbb{Z}_{>0} \rightarrow \mathbb{Z}_{>0}$ such that  $$ m^{2}+f(n) \mid m f(m)+n $$  for all positive integers $m$ and $n$.  (Malaysia)
-/
theorem NumberTheory_n1 (f : ℕ → ℕ) (hf : ∀ n > 0, f n 
 > 0):
    (∀ m > 0, ∀ n > 0, m^2 + f n ∣ m * f m + n) ↔
    (∀ n > 0, f n = n) := by 
  apply Iff.intro
  · intro H
    -- Setting $m=n=2$ tells us that $4+f(2) \mid 2 f(2)+2$.
    obtain ⟨k, hk⟩ := H 2 (by linarith) 2 (by linarith)
    -- Since $2 f(2)+2<2(4+f(2))$, we must have $2 f(2)+2=4+f(2)$, so $f(2)=2$.
    have : 2 * f 2 + 2 < 2 * (2 ^ 2 + f 2) := by linarith
    have : 2 * (f 2) + 2 > 0 := by linarith
    -- showing 2 * f 2 + 2 = 2 * (2 ^ 2 + f 2) is equivalent to showing k = 1
    have : k = 1 := by 
      rcases (by omega : k = 0 ∨ k = 1 ∨ k > 1) with h1 | h2 | h3
      · simp [h1] at hk
      · exact h2
      · have : k ≥ 2 := by omega
        have : (2 ^ 2 + f 2) * k ≥ (2 ^ 2 + f 2) * 2 := by 
          rw [mul_comm _ 2, mul_comm _ k]
          apply mul_le_mul
          all_goals linarith
        omega
    simp only [Nat.reducePow, this, mul_one] at hk
    have crux1 : ∀ n > 0, f n ≤ n := by 
      intro n hn
      -- Plugging in $m=2$ then tells us that $4+f(n) \mid 4+n$, 
      specialize H 2 (by linarith) n hn
      have : f 2  = 2 := by linarith
      rw [this] at H
      simp only [Nat.reducePow, Nat.reduceMul] at H
      obtain ⟨k, hk⟩ := H
      have : k > 0 := by nlinarith
      --  which implies that $f(n) \leqslant n$ for all $n$.
      nlinarith
    have crux2 : ∀ n ≥ 2, f n ≥ n := by 
      intro n hn
      -- Setting $m=n$ gives $n^{2}+f(n) \mid n f(n)+n$, so $n f(n)+n \geqslant n^{2}+f(n)$ which we rewrite as $(n-1)(f(n)-n) \geqslant 0$.
      obtain ⟨k, hk⟩ := H n (by linarith) n (by linarith)
      have : n * f n + n ≥ (n ^ 2 + f n) := by
        have : k > 0 := by nlinarith
        nlinarith
      -- Therefore $f(n) \geqslant n$ for all $n \geqslant 2$.
      nlinarith
    intro n hn
    -- using the above crux lemmas we now proceed to prove the equality for all n > 0
    rcases (by omega : n = 1 ∨ n ≥ 2) with h1 | h2 
    -- This is trivially true for $n=1$ since f n ≥ 1 and f n ≤ 1 from crux1
    · have := hf n (by linarith)
      specialize crux1 n (by linarith)
      linarith
    -- in case where n ≥ 2, we combine crux1 and crux2 to get the equality
    · specialize crux1 n (by linarith)
      specialize crux2 n (by linarith)
      linarith
  · intro H
    intro m hm n hn
    rw [H m hm, H n hn, show m*m = m^2 by ring]