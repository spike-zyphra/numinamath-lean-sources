import Mathlib

/-Given is an unknown sequence $a_{1}, a_{2}, a_{3}, \ldots$ of integers that satisfies the following property: for every prime number $p$ and every positive integer $k$ it holds that

$$
a_{p k+1}=p a_{k}-3 a_{p}+13
$$

Determine all possible values of $a_{2013}$.-/
theorem number_theory_168484 (a : ℕ → ℤ) (ha : ∀ p k, Nat.Prime p → k > 0 → a (p * k + 1) = p * a k - 3 * a p + 13) :
    a 2013 = 2016 := by
    -- Laat $q$ en $t$ priemgetallen zijn. 
    -- waaruit volgt
    -- $$ t a_{q}-3 a_{t}=q a_{t}-3 a_{q} $$
    have h1 : ∀ q t : ℕ, Nat.Prime q → Nat.Prime t → ((t * a q - 3 * a t) = (q * a t - 3 * a q)) := by
      intro q t hq ht
      -- Vul in $k=q, p=t$ :
      -- $$ a_{q t+1}=t a_{q}-3 a_{t}+13 $$
      have h2 := ha q t hq (Nat.Prime.pos ht)
      -- Vul ook in $k=t, p=q$ :
      -- $$ a_{q t+1}=q a_{t}-3 a_{q}+13 $$
      have h3 := ha t q ht (Nat.Prime.pos hq)
      -- Beide uitdrukkingen rechts zijn dus gelijk aan elkaar
      rw [mul_comm,h3] at h2
      linarith
    -- oftewel
    -- $$ (t+3) a_{q}=(q+3) a_{t} . $$
    have h4 : ∀ q t : ℕ, Nat.Prime q → Nat.Prime t → ((t + 3) * a q = (q + 3) * a t) := by
      intro q t hq ht
      specialize h1 q t hq ht
      linarith
    -- In het bijzonder geldt $5 a_{3}=6 a_{2}$ en $5 a_{7}=10 a_{2}$. 
    have h5 := h4 3 2 (Nat.prime_three) (Nat.prime_two)
    have h6 := h4 2 7 (Nat.prime_two) ( Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl)
    norm_num at h5 h6
    -- Vul nu $k=3$, $p=2$ in:
    -- $$ a_{7}=2 a_{3}-3 a_{2}+13=2 \cdot \frac{6}{5} a_{2}-3 a_{2}+13 . $$
    have h7 : a 7 = (2 * (6 / 5 : ℚ) - 3) * a 2 + 13 := by
      specialize ha 2 3 (Nat.prime_two) (Nat.Prime.pos (Nat.prime_three))
      norm_num at ha
      rw [ha]
      have : ↑(5:ℤ) = (5:ℚ) := rfl
      have h8 : a 3 = (6 / 5 : ℚ) * a 2 := by
        field_simp ;rw [← this,← Int.cast_mul,mul_comm,h5] ;simp
      simp [h8] ;ring
    norm_num at h7
    -- Omdat $a_{7}=\frac{10}{5} a_{2}$, vinden we nu
    -- $$ \frac{13}{5} a_{2}=13 $$
    -- dus $a_{2}=5$.
    have h12 : a 2 = 5 := by
      have h9 : 2 * a 2 = a 7 := by omega
      rw [← h9] at h7 ;simp at h7
      have h10 : 2 * ↑(a 2) + ((3 / 5:ℚ) * ↑(a 2)) = 13 := by linarith
      rw [← add_mul] at h10 ;norm_num at h10
      have h11 : a 2 = (13 / 5:ℚ)⁻¹ * 13 := by nth_rewrite 2 [← h10] ;ring
      norm_num at h11
      exact_mod_cast h11
    -- Nu geldt voor elk priemgetal $p$ dat $a_{p}=\frac{(p+3) a_{2}}{5}=p+3$.
    have h13 : ∀ x : ℕ, Nat.Prime x → a x = x + 3 := by
      intro p hp 
      specialize h4 2 p (Nat.prime_two) hp
      simp [h12] at h4
      linarith
    -- Vul in $k=4, p=3$ :
    -- $$ a_{13}=3 a_{4}-3 a_{3}+13 \text {. } $$
    have h14 := ha 3 4 (by norm_num) (by norm_num)
    norm_num at h14
    -- We weten dat $a_{13}=16$ en $a_{3}=6$, dus dit geeft $3 a_{4}=21$, oftewel $a_{4}=7$.
    have h15 : a 3 = 6 := by 
      specialize h13 3 (by norm_num)
      omega
    have h16 : a 13 = 16 := by
      specialize h13 13 (by norm_num)
      omega
    rw [h15,h16] at h14
    have h17 : a 4 = 7 := by linarith
    -- Vul ten slotte $k=4$ en $p=503$ in:
    -- $a_{2013}=a_{4 \cdot 503+1}=503 \cdot a_{4}-3 a_{503}+13=503 \cdot 7-3 \cdot(503+3)+13=503 \cdot 4-9+13=2016$.
    specialize ha 503 4 (by norm_num) (by norm_num)
    specialize h13 503 (by norm_num)
    rw [h13,h17] at ha
    norm_num at ha ;exact ha



        