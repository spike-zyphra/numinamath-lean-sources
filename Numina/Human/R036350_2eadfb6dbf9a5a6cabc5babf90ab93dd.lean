import Mathlib

theorem Nat.pow_eq_one : ∀ {a n : ℕ}, a ^ n = 1 ↔ a = 1 ∨ n = 0 :=
fun {a n} =>
  Or.casesOn (eq_or_ne n 0)
    (fun h =>
      Eq.symm h ▸
        of_eq_true
          (Eq.trans (congr (congrArg Iff (eq_self 1)) (Eq.trans (congrArg (Or (a = 1)) (eq_self 0)) (or_true (a = 1))))
            (iff_self True)))
    fun hn =>
    Eq.mpr (id (congrArg (Iff (a ^ n = 1)) (Eq.trans (congrArg (Or (a = 1)) (eq_false hn)) (or_false (a = 1)))))
      (Eq.mp (congrArg (fun x => a ^ n = x ↔ a = 1) (Nat.one_pow n)) 
      (by simp; exact pow_eq_one_iff hn))

/-Man finde alle Quadrupel positiver ganzer Zahlen ( $m, n, p, q$ ) mit der Eigenschaft

$$
p^{m} q^{n}=(p+q)^{2}+1
$$-/
theorem number_theory_604234 (m n p q : ℕ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) :
p ^ m * q ^ n = (p + q) ^ 2 + 1 ↔ ((m = 1 ∧ n = 2 ∧ p = 2 ∧ q = 5) ∨ (m = 1 ∧ n = 2 ∧ p = 13 ∧ q = 5) ∨
(m = 2 ∧ n = 1 ∧ p = 5 ∧ q = 2) ∨ (m = 2 ∧ n = 1 ∧ p = 5 ∧ q = 13) ) := by
-- According to the reference answer, we first need to prove the following lemma
  have lm : ∀ k l : ℕ, 0 < k → 0 < l → k * l ∣ k ^ 2 + l ^ 2 + 1 → (k ^ 2 + l ^ 2 + 1) / (k * l) = 3 := by
  -- Introduce variables and rewrite the division assumption
    intro k l kpos lpos hdvd; rcases hdvd with ⟨a, ha⟩; rw [ha, Nat.mul_div_cancel_left]
  -- Prepare to use Nat.find
    have sumkl : ∃ t, ∃ k l, t = k + l ∧ k ^ 2 + l ^ 2 + 1 = k * l * a := by use k+l; use k; use l
    have dcpr : DecidablePred fun n => ∃ k l, n = k + l ∧ k ^ 2 + l ^ 2 + 1 = k * l * a := by apply Classical.decPred
  -- Let $k'$, $l'$ be satisfying $k'^2+l'^2+1=k'*l' *a$ whose sum $k'+l'$ is smallest
  -- Assume w. l. o. g. that $l'$ is less or equal to $h'$, we are going to show $l'=k'$ by finding a contradiction if we assume $l'< k'$
    obtain ⟨k', l', hsum, heq⟩ := Nat.find_spec sumkl; wlog llek : l' ≤ k'
    · specialize this m n p q hm hn hp hq k l kpos lpos a ha sumkl dcpr l' k' (by rw [add_comm]; exact hsum)
      specialize this (by nth_rw 2 [add_comm]; nth_rw 2 [mul_comm]; exact heq) (show _ by linarith)
      exact this
  -- $Nat.find sumkl$ is the smallest sum among all numbers with this property
    have leiff := Nat.find_le_iff sumkl; rw [hsum] at leiff
  -- Make a copy heq' of heq and rewrite heq' to a product form
    let heq' := heq; symm at heq'; rw [add_assoc, ← Nat.sub_eq_iff_eq_add', pow_two] at heq'
    rw [mul_assoc, ← Nat.mul_sub] at heq'
  -- Prove all the positivity results we need
    have apos : 0 < a := by by_contra!; simp at this; simp [this] at ha
    have k'pos : 0 < k' := by by_contra!; simp at this; simp [this] at heq
    have l'pos : 0 < l' := by by_contra!; simp at this; simp [this] at heq
  -- Prove that $k'$ divides $l'^2+1$
    have auxdvd : k' ∣ l' ^ 2 + 1 := by use (l' * a - k'); symm; exact heq'
  -- Splite $l'≤k'$ to $l'< k'$ or $l'=k'$
    rw [le_iff_lt_or_eq] at llek; rcases llek with lltk|leqk
    -- If $l'< k'$, let $k''$ be $a *l'-k'$ and prove $k''+l'$ is a strict smaller sum than $k'+l'$, which contradicts to our choice for $k'+l'$
    · let k'' := a * l' - k'; have hk''1 : k'' = (l' ^ 2 + 1) / k' := by
        apply Nat.eq_div_of_mul_eq_left; positivity; simp [k'']; rw [← heq']; ring_nf
      have hk''2 : l' ^ 2 + k'' ^ 2 + 1 = l' * k'' * a := by
        simp [k'']; zify; repeat rw [Nat.cast_sub]
        push_cast; ring_nf; norm_cast; nth_rw 2 [mul_comm]; rw [← mul_assoc, ← heq, Int.subNatNat_eq_coe]
        nth_rw 3 [mul_comm]; rw [← mul_assoc, ← heq]; push_cast; ring
        apply le_of_lt; rw [← Nat.sub_pos_iff_lt, mul_comm, ← mul_lt_mul_left k'pos, heq']; simp
      have := (leiff (l'+k'')).mpr (by use l'+k''; split_ands; rfl; use l'; use k'')
      rw [add_comm, add_le_add_iff_left] at this; suffices : k'' < k'; linarith
      rw [hk''1, Nat.div_lt_iff_lt_mul k'pos, ← add_lt_add_iff_left (2*l')]
      rw [Nat.lt_iff_add_one_le] at lltk; calc
        _ = (l' + 1) ^ 2 := by ring
        _ ≤ k' ^ 2 := by rw [Nat.pow_le_pow_iff_left]; exact lltk; simp
        _ < _ := by simp [pow_two]; linarith
  -- Now we have $l'=k'$, rearranging terms on heq shows $k'=1$ and $a-2=1$, which is exactly what we want to prove
    rw [leqk] at heq; ring_nf at heq; symm at heq; rw [← Nat.sub_eq_iff_eq_add, ← Nat.mul_sub] at heq
    simp at heq; rcases heq with ⟨_,hr⟩; rw [Nat.sub_eq_iff_eq_add] at hr; any_goals linarith
    apply le_of_lt; rw [← Nat.sub_pos_iff_lt, hr]; simp
    rw [← heq, add_assoc]; simp; positivity
-- To prove the main goal, we first rewrite the equation and rearrange its terms
  constructor
  · intro heq; rw [add_comm, add_sq', ← add_assoc, ← add_assoc, ← Nat.sub_eq_iff_eq_add (by simp [heq])] at heq
    rw [show m = m-1+1 by rw [Nat.sub_add_cancel]; linarith, show n = n-1+1 by rw [Nat.sub_add_cancel]; linarith] at heq
    rw [pow_succ, mul_assoc, pow_succ'] at heq; nth_rw 2 [← mul_assoc, mul_comm] at heq
    rw [← mul_assoc] at heq; nth_rw 2 [mul_assoc] at heq; rw [← Nat.sub_mul, add_assoc, add_comm] at heq
  -- Prove the division relation which is required by lm, then specialize lm to $p$, $q$ and find $p^(m-1)*q^(n-1)$ is $5$
    have pqdvd : p * q ∣ p ^ 2 + q ^ 2 + 1 := by use (p ^ (m - 1) * q ^ (n - 1) - 2); rw [← heq]; ring
    specialize lm p q hp hq pqdvd; rw [← heq, Nat.mul_div_cancel, Nat.sub_eq_iff_eq_add] at lm
    norm_num at lm; have pdvd : p ^ (m - 1) ∣ 5 := by use q ^ (n - 1); rw [← lm]
    simp [Nat.dvd_prime Nat.prime_five, or_assoc, Nat.pow_eq_one] at pdvd; rcases pdvd with h1|h2|h3
    -- Discuss all the possibilities, if $p=1$ then we have $q$ divides $2$ so $q$ is $1$ or $2$
    -- but both cases can't happen for trivial reasons
    · simp [h1] at *; rw [add_comm, ← add_assoc, pow_two, ← Nat.dvd_add_iff_left] at pqdvd
      norm_num at pqdvd; rw [Nat.dvd_prime Nat.prime_two] at pqdvd; rcases pqdvd; all_goals simp_all
      by_cases h' : n ≤ 1
      · replace h' : n = 1 := by linarith
        simp [h'] at lm
      suffices : Even 5; contradiction; rw [← lm, Nat.even_pow']; simp
      rw [Nat.ne_zero_iff_zero_lt, Nat.lt_sub_iff_add_lt]; all_goals linarith
    -- If $m=1$, prove that $n=2$, $q=5$ and $p=2$ or $p=13$
    · rw [Nat.sub_eq_zero_iff_le] at h2; replace h2 : m = 1 := by linarith
      simp [h2] at *; by_cases h' : n ≤ 1
      · replace h' : n = 1 := by linarith
        simp [h'] at lm
      have : q ∣ 5 := by
        rw [← lm]; apply dvd_pow; rfl
        rw [Nat.ne_zero_iff_zero_lt, Nat.lt_sub_iff_add_lt]; all_goals linarith
      rw [Nat.dvd_prime Nat.prime_five] at this; rcases this with hl|hr; simp [hl] at *
      · simp [hr] at *; rw [Nat.pow_eq_self_iff, Nat.sub_eq_iff_eq_add] at lm
        simp [lm] at *; rw [mul_comm, mul_assoc, add_assoc] at heq; norm_num at heq
        have : p ∈ Nat.divisors 26 := by
          simp; rw [Nat.dvd_add_iff_right (show p ∣ p^2 by use p; ring), ← heq]; simp
        rw [show Nat.divisors 26 = {1,2,13,26} by decide] at this; simp at this
        rcases this with _|_|_|_; all_goals simp_all
    -- If $p^(m-1)=5$, then $q=1$ or $n=1$
    · rw [h3, Nat.mul_eq_left (by simp)] at lm; simp [Nat.pow_eq_one] at lm; rcases lm with _|hr
      -- If $q=1$, we have $p$ divides $2$ so $p$ is $1$ or $2$, but both cases can't happen for trivial reasons
      · simp_all; rw [add_assoc, ← Nat.dvd_add_iff_right (by use p; ring)] at pqdvd
        norm_num at pqdvd; rw [Nat.dvd_prime Nat.prime_two] at pqdvd; rcases pqdvd; all_goals simp_all
        by_cases h' : m ≤ 1
        · replace h' : m = 1 := by linarith
          simp [h'] at h3
        suffices : Even 5; contradiction; rw [← h3, Nat.even_pow']; simp
        rw [Nat.ne_zero_iff_zero_lt, Nat.lt_sub_iff_add_lt]; all_goals linarith
    -- If $n=1$, prove that $m=2$, $p=5$ and $q=2$ or $q=13$
      rw [Nat.sub_eq_zero_iff_le] at hr; replace hr : n = 1 := by linarith
      simp [hr] at *; simp [h3] at heq; by_cases h' : m ≤ 1
      · replace h' : m = 1 := by linarith
        simp [h'] at h3
      have : p ∣ 5 := by
        rw [← h3]; apply dvd_pow; simp
        rw [Nat.ne_zero_iff_zero_lt, Nat.lt_sub_iff_add_lt]; all_goals linarith
      rw [Nat.dvd_prime Nat.prime_five] at this; rcases this with hl|hr; simp [hl] at *
      simp [hr] at *; rw [Nat.pow_eq_self_iff, Nat.sub_eq_iff_eq_add] at h3; simp [h3] at *
      rw [← mul_assoc, add_comm, ← add_assoc] at heq; norm_num at heq
      have : q ∈ Nat.divisors 26 := by
        simp; rw [Nat.dvd_add_iff_left (show q ∣ q^2 by use q; ring), ← heq]; simp
      rw [show Nat.divisors 26 = {1,2,13,26} by decide] at this; simp at this
      rcases this with _|_|_|_; all_goals simp_all
    apply le_of_lt; rw [← Nat.sub_pos_iff_lt, lm]; simp; positivity
-- Conversely, it is straightforward to check that these values for $p$, $q$, $m$ and $n$ satisfy the equation
  intro h; rcases h with ⟨_,_,_,_⟩|⟨_,_,_,_⟩|⟨_,_,_,_⟩|⟨_,_,_,_⟩; all_goals simp_all