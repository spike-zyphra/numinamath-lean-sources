import Mathlib

/-For each positive integer $n$ and non-negative integer $k$, define $W(n, k)$ recursively by

$$
W(n, k)= \begin{cases}n^{n} & k=0 \\ W(W(n, k-1), k-1) & k>0\end{cases}
$$

Find the last three digits in the decimal representation of $W(555,2)$.-/
theorem number_theory_609532 (W : ℕ → ℕ → ℕ) (hW1 : ∀ n, W n 0 = n ^ n)
  (hW2 : ∀ n k, W n (k+1) = W (W n k) k) :
  W 555 2 % 1000 = 875 := by
  -- For any $n$, we have
  -- $$ W(n, 1)=W(W(n, 0), 0)=\left(n^{n}\right)^{n^{n}}=n^{n^{n+1}} $$
  have h1 : ∀ n, W n 1 = n ^ (n ^ (n + 1)) := by
    intro n
    specialize hW2 n 0
    simp at hW2
    rw [hW2,hW1 n,hW1 (n^n),← Nat.pow_mul,Nat.pow_add,pow_one,mul_comm]
  --Thus,$$ W(555,1)=555^{555^{556}} $$
  have h2 := h1 555
  -- Let $N=W(555,1)$ for brevity, and note that $N \equiv 0(\bmod 125)$, and $N \equiv 3(\bmod 8)$.
  let N := W 555 1
  have h3 : N % 125 = 0 := by
    simp only [N,h2]
    apply Nat.dvd_iff_mod_eq_zero.mp
    have : 125 = 5 ^ 3 := by norm_num
    have this' : 555 = 5 * 111 := by norm_num
    nth_rewrite 1 [this,this',mul_pow]
    apply dvd_mul_of_dvd_left
    apply pow_dvd_pow
    norm_num

  have h4 : N % 8 = 3 := by
    let M := 555 ^ (555 + 1)
    have : 555 ^ M = N := by simp only [N,h2]
    rw [← this,Nat.pow_mod] ;simp only [M]
    have : 555 % 8 = 3 := by norm_num
    rw [this]
    have : 555 ^ (555 + 1) % 2 = 1 := by
      rw [Nat.pow_mod]
      have : 555 % 2 = 1 := by norm_num
      rw [this] ;simp
    have : 2 ∣ (555 ^ (555 + 1) - 1) := by
      refine Nat.dvd_of_mod_eq_zero ?_
      exact Nat.sub_mod_eq_zero_of_mod_eq this
    rcases this with ⟨k, h⟩
    have : 555 ^ (555 + 1) = 2 * k + 1 := by
      refine (Nat.sub_eq_iff_eq_add ?_).mp h
      norm_num
    rw [this,pow_add,pow_one,pow_mul,Nat.mul_mod,Nat.pow_mod]
    norm_num

  -- Then,$$ W(555,2)=W(N, 1)=N^{N^{N+1}} $$ is $0(\bmod 125)$ and $3(\bmod 8)$.
  have h5 : W 555 2 = N ^ N ^ (N + 1) := by
    have := hW2 555 1
    simp at this
    rw [this]
    specialize h1 N
    rw [h1]
  have h6 : W 555 2 % 125 = 0 := by
    rw [h5,Nat.pow_mod,h3,zero_pow] ;simp ;simp
    simp only [N,h2] ;apply pow_ne_zero ;simp
  have h7 : W 555 2 % 8 = 3 := by
    rw [h5,Nat.pow_mod,h4]
    have : Odd  (N ^ (N + 1)) := by
      apply Odd.pow
      simp only [N,h2]
      apply Odd.pow ;use 277 ;norm_num
    rcases this with ⟨k, h⟩
    rw [h,pow_add,pow_one,Nat.mul_mod,pow_mul,Nat.pow_mod]
    norm_num
  -- From this we can conclude (by the Chinese Remainder Theorem) that the answer is 875 .
  have hmn : Nat.Coprime 125 8 := by norm_num
  have hm : W 555 2 ≡ 875 [MOD 125] := by
    exact h6
  have hn : W 555 2 ≡ 3 [MOD 8] := by
    exact h7
  have h8 := (Nat.modEq_and_modEq_iff_modEq_mul hmn).mp ⟨hm,hn⟩
  norm_num at h8
  exact h8