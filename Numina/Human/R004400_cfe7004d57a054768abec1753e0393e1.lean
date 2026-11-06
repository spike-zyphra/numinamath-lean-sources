import Mathlib

/- Determine all finite nonempty sets $S$ of positive integers satisfying

$$
\frac{i+j}{(i, j)} \text { is an element of } S \text { for all } i, j \text { in } S
$$

where $(i, j)$ is the greatest common divisor of $i$ and $j$.

Answer: $S=\{2\}$.

# -/
theorem number_theory_260851 :
    {S : Finset ℕ | S.Nonempty ∧ (∀ i ∈ S, 0 < i) ∧ ∀ i ∈ S, ∀ j ∈ S, (i + j) / i.gcd j ∈ S} = {{2}} := by
  ext S
  simp
  constructor
  swap
  -- We verify that $S = \{2\}$ is a solution.
  . rintro rfl
    simp
  rintro ⟨⟨k₀, hk₀⟩, h₁, h₂⟩
  -- We first prove that $2 \in S$.
  have h₃ : 2 ∈ S := by
    -- Take $i = j = k_0$.
    simpa [show 0 < k₀ from h₁ k₀ hk₀] using h₂ k₀ hk₀ k₀ hk₀
  -- We now prove that $S$ is a set of even numbers.
  have h₄ : ∀ x ∈ S, Even x := by
    -- If $S$ is not a set of even numbers, then there exists an odd number $k$ in $S$.
    by_contra! h₄
    simp at h₄
    -- So the set of odd numbers in $S$ is nonempty.
    rw [← Finset.filter_nonempty_iff] at h₄
    -- We take the maximum odd number $k$ in $S$.
    let k := (Finset.filter Odd S).max' h₄
    have hk₀ : k ∈ Finset.filter Odd S := Finset.max'_mem (Finset.filter Odd S) h₄
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_filter.mp hk₀
    -- Since $k$ is odd, we have $\gcd(k, 2) = 1$.
    have hk₃ : k.gcd 2 = 1 := Nat.coprime_two_right.mpr hk₂
    -- We take $i = k$ and $j = 2$.
    specialize h₂ k hk₁ 2 h₃
    -- So $k + 2$ is in $S$.
    simp [hk₃] at h₂
    -- Since $k + 2$ is odd, it is also in the set of odd numbers in $S$.
    have h₆ : k + 2 ∈ Finset.filter Odd S := by
      simp [h₂]
      exact Odd.add_even hk₂ (by simp)
    -- But it contradicts the maximality of $k$.
    have h₇ : k + 2 ≤ k := Finset.le_max' (Finset.filter Odd S) (k + 2) h₆
    simp at h₇
  -- We now prove that the only element in $S$ is $2$.
  have h₅ : ∀ x ∈ S, x = 2 := by
    -- If otherwise, $S$ remains nonempty after erasing $2$.
    by_contra! h₅
    rw [← Finset.filter_nonempty_iff, Finset.filter_ne'] at h₅
    -- Let $l$ be the minimum element in $S$ that is not $2$.
    let l := (S.erase 2).min' h₅
    have hl₀ : l ∈ S.erase 2 := Finset.min'_mem (S.erase 2) h₅
    rcases Finset.mem_erase.mp hl₀ with ⟨hl₁, hl₂⟩
    -- Since $l$ is even by the previous step, we have $l = 2s$ for some $s$.
    rcases h₄ l hl₂ with ⟨s, hs⟩
    rw [show s + s = 2 * s by ring] at hs
    -- Since $l$ is a positive integer not equal to $2$, we have $1 < s$.
    have hs₁ : 1 < s := by
      specialize h₁ l hl₂
      rw [hs] at h₁ hl₁
      omega
    -- We take $i = l$ and $j = 2$.
    specialize h₂ l hl₂ 2 h₃
    -- We get that $s + 1$ is in $S$.
    simp [hs] at h₂
    -- Since $1 < s$, we have $s + 1 \neq 2$.
    have h₆ : s + 1 ∈ S.erase 2 := by
      simp [h₂, Nat.ne_of_lt' hs₁]
    -- But $s + 1 < l = 2s$, so it contradicts the minimality of $l$.
    have h₇ : l ≤ s + 1 := Finset.min'_le (S.erase 2) (s + 1) h₆
    omega
  -- Trivial after the lemmas `h₃`, `h₅` above.
  aesop