import Mathlib

open Finset Real

/-- Let $f(x) = x^{2}(1-x)^{2}$. What is the value of the sum \[f \left(\frac{1}{2019} \right)-f
\left(\frac{2}{2019} \right)+f \left(\frac{3}{2019} \right)-f \left(\frac{4}{2019} \right)+\cdots +
f \left(\frac{2017}{2019} \right) - f \left(\frac{2018}{2019} \right)?\]

$\textbf{(A) }0\qquad\textbf{(B) }\frac{1}{2019^{4}}\qquad\textbf{(C) }\frac{2018^{2}}{2019^{4}}
\qquad\textbf{(D) }\frac{2020^{2}}{2019^{4}}\qquad\textbf{(E) }1$ -/
theorem algebra_93389 {f : ℝ → ℝ} (hf : ∀ x, f x = x^2 * (1 - x)^2) :
    ∑ i ∈ (Icc (1:ℕ) 2018), f (i / 2019) * (-1 : ℝ)^(i + 1) = 0 := by

  -- First note that $f(x) = f(1 - x)$.
  have {x : ℝ} : f x = f (1 - x) := by
    -- We can see this since
    -- $f(x) = x^2 (1 - x)^2 = (1 - x)^2 x^2 = (1 - x)^2 (1 - (1 - x))^2 = f(1 - x)$.
    calc _ = x^2 * (1 - x)^2 := by rw [hf]
         _ = (1 - x)^2 * x^2 := by ring
         _ = (1 - x)^2 * (1 - (1 - x))^2 := by ring
         _ = f (1 - x) := by rw [hf]

  -- For simplicity, let $a_i = f (i / 2019)$
  let a (i : ℕ) := f (i / 2019)
  -- We will show that $\sum_{i = 1}^{2018} a_i (-1)^{i + 1} = 0$.
  show ∑ i ∈ Icc 1 2018, a i * (-1 : ℝ)^(i + 1) = 0

  -- It is enough to show that $2 \cdot \sum_{i = 1}^{2018} a_i (-1)^{i + 1} = 0$.
  suffices 2 * ∑ i ∈ Icc 1 2018, (a i) * (-1)^(i + 1) = 0 from by linarith

  -- So, we have $a_i = a_{2019 - i}$.
  have ha {i : ℕ} (hi : i ∈ Icc 1 2018) : a i = a (2019 - i) := by
    simp [a]
    simp at hi
    rw [this, Nat.cast_sub (by omega)]
    congr
    ring

  -- Writing the same sum in reverse, does not change the sum, so we have
  -- $\sum_{i = 1}^{2018} a_i (-1)^{i + 1} = \sum_{i = 1}^{2018} a_{2019 - i} (-1)^{2018 - i}$.
  have hr : ∑ i ∈ Icc 1 2018, (a i) * (-1)^(i + 1) = ∑ i ∈ Icc 1 2018, (a (2019 - i)) * (-1)^(2018 - i) := by
    apply Finset.sum_bij (fun i _ ↦ 2019 - i)
    · intro i hi
      simp at hi ⊢
      omega
    · intro i hi j hj h
      simp at hi hj
      omega
    · intro i hi
      simp at hi ⊢
      exact ⟨2019 - i, by omega⟩
    · intro i hi
      simp at hi ⊢
      congr 1
      · congr; omega
      · rw [(by omega : 2018 - (2019 - i) = i - 1)]
        suffices (-(1:ℝ))^1 * (-1)^(i + 1) = (-1)^1 * (-1)^(i - 1) by simpa using this
        rw [←pow_add, ←pow_add, (by omega : 1 + (i - 1) = i)]
        ring

  -- When $i$ is even $(-1)^{i + 1} + (-1)^{2018 - i} = -1 + 1 = 0$. When $i$ is odd
  -- $(-1)^{i + 1} + (-1)^{2018 - i} = 1 - 1 = 0$. Therefore, the expression
  -- $(-1)^{i + 1} + (-1)^{2018 - i}$ is always $0$.
  have {i : ℕ} (hi : i ∈ Icc 1 2018) : (-(1:ℝ))^(i + 1) + (-1)^(2018 - i) = 0 := by
    simp at hi
    rcases (Nat.even_or_odd' i) with ⟨a, (ha | ha)⟩
    · have : 2 ∣ (2018 - i) := by omega
      rcases this with ⟨b, hb⟩
      rw [hb, ha]
      calc _ = (-(1:ℝ))^(2 * a) * (-1)^1 + (-1)^(2*b) := by ring
           _ = ((-1)^2)^a * (-1)^1 + (-1)^(2*b) := by simp
           _ = ((-1)^2)^a * (-1)^1 + ((-1)^2)^b := by simp
           _ = _ := by simp

    · have : ¬ 2 ∣ 2018 - i := by intro h; omega
      have : ¬ Even (2018 - i) := by intro h; apply this; exact even_iff_two_dvd.mp h
      have : Odd (2018 - i) := by exact Nat.not_even_iff_odd.mp this
      have : ∃ b, 2018 - i = 2 * b + 1 := by simpa using this
      rcases this with ⟨b, hb⟩
      rw [hb, ha]
      calc _ = (-(1:ℝ))^(2 * (a + 1)) + (-1)^(2 * b + 1) := by congr 1
           _ = ((-1)^2)^(a + 1) + (-1)^(2 * b + 1) := by simp
           _ = ((-1)^2)^(a + 1) + (-1)^(2 * b) * (-1)^1 := by ring
           _ = ((-1)^2)^(a + 1) + ((-1)^2)^b * (-1)^1 := by simp
           _ = _ := by simp

  -- Let's compute $2 \cdot \sum_{i = 1}^{2018} a_i (-1)^{i + 1} = 0$
  -- $2 \sum_{i = 1}^{2018} a_i (-1)^{i + 1} = $\sum_{i = 1}^{2018} a_i (-1)^{i + 1} + \sum_{i = 1}^{2018} a_i (-1)^{i + 1}$
  calc _ = ∑ i ∈ Icc 1 2018, (a i) * (-1)^(i + 1) + ∑ i ∈ Icc 1 2018, (a i) * (-1)^(i + 1) := by ring
  -- Writing the second sum in reverse:
  -- = $\sum_{i = 1}^{2018} a_i (-1)^{i + 1} + \sum_{i = 1}^{2018} a_{2019 - i} (-1)^{2018 - i}$
       _ = ∑ i ∈ Icc 1 2018, (a i) * (-1)^(i + 1) + ∑ i ∈ Icc 1 2018, (a (2019 - i)) * (-1)^(2018 - i) := by rw [hr]
  -- Combining the summatation symbols:
  -- = $\sum_{i = 1}^{2018} (a_i (-1)^{i + 1} + a_{2019 - i} (-1)^{2018 - i})$
       _ = ∑ i ∈ Icc 1 2018, ((a i) * (-1)^(i + 1) + (a (2019 - i)) * (-1)^(2018 - i)) := by rw [sum_add_distrib]
  -- We know that $a_i = a_{2019 - i}$, so:
  -- = $\sum_{i = 1}^{2018} (a_i (-1)^{i + 1} + a_i (-1)^{2018 - i})$
       _ = ∑ i ∈ Icc 1 2018, ((a i) * (-1)^(i + 1) + (a i) * (-1)^(2018 - i)) := by apply sum_congr rfl; intro i hi; congr 2; rw [ha hi]
  -- Take the common factor $a_i$ to the front:
  -- = $\sum_{i = 1}^{2018} a_i ((-1)^{i + 1} + (-1)^{2018 - i})$
       _ = ∑ i ∈ Icc 1 2018, (a i) * ((-1)^(i + 1) + (-1)^(2018 - i)) := by simp_rw [mul_add]
  -- When $i$ is even $(-1)^{i + 1} + (-1)^{2018 - i} = -1 + 1 = 0$. When $i$ is odd
  -- $(-1)^{i + 1} + (-1)^{2018 - i} = 1 - 1 = 0$. Therefore, the sum is $0$.
       _ = ∑ i ∈ Icc 1 2018, (a i) * 0 := by apply sum_congr rfl; intro i hi; congr; apply this hi
        _ = 0 := by simp