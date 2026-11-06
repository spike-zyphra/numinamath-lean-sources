import Mathlib
def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 => 4 * a (n + 1) + a n

namespace backport
open Nat
lemma dvd_mul_left_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ c * b :=
  Nat.dvd_trans h (Nat.dvd_mul_left _ _)

lemma gcd_eq_one_iff {m n : Nat} : Nat.gcd m n = 1 ↔ ∀ c, c ∣ m → c ∣ n → c = 1 := by
  simp [gcd_eq_iff]

lemma gcd_right_eq_iff {m n n' : Nat} : Nat.gcd m n = Nat.gcd m n' ↔ ∀ k, k ∣ m → (k ∣ n ↔ k ∣ n') := by
  refine ⟨fun h k hkm => ⟨fun hkn => ?_, fun hkn' => ?_⟩, fun h => Nat.dvd_antisymm ?_ ?_⟩
  · exact Nat.dvd_trans (h ▸ Nat.dvd_gcd hkm hkn) (Nat.gcd_dvd_right m n')
  · exact Nat.dvd_trans (h ▸ Nat.dvd_gcd hkm hkn') (Nat.gcd_dvd_right m n)
  · exact Nat.dvd_gcd_iff.2 ⟨Nat.gcd_dvd_left _ _, (h _ (Nat.gcd_dvd_left _ _)).1 (Nat.gcd_dvd_right _ _)⟩
  · exact Nat.dvd_gcd_iff.2 ⟨Nat.gcd_dvd_left _ _, (h _ (Nat.gcd_dvd_left _ _)).2 (Nat.gcd_dvd_right _ _)⟩

lemma gcd_mul_right_right_of_gcd_eq_one {n m k : Nat} : Nat.gcd n m = 1 → Nat.gcd n (m * k) = Nat.gcd n k := by
  rw [gcd_right_eq_iff, gcd_eq_one_iff]
  refine fun h l hl₁ => ⟨?_, fun a => dvd_mul_left_of_dvd a m⟩
  rw [Nat.dvd_mul]
  rintro ⟨k₁, k₂, hk₁, hk₂, rfl⟩
  obtain rfl : k₁ = 1 := h _ (Nat.dvd_trans (Nat.dvd_mul_right k₁ k₂) hl₁) hk₁
  simpa

lemma gcd_mul_left_right_of_gcd_eq_one {n m k : Nat} (h : Nat.gcd n m = 1) :
    Nat.gcd n (k * m) = Nat.gcd n k := by
  rw [Nat.mul_comm, gcd_mul_right_right_of_gcd_eq_one h]

lemma gcd_mul_right_left_of_gcd_eq_one {n m k : Nat} (h : Nat.gcd n m = 1) :
    Nat.gcd (n * k) m = Nat.gcd k m := by
  rw [gcd_comm, gcd_mul_right_right_of_gcd_eq_one (gcd_comm _ _ ▸ h), gcd_comm]
end backport

lemma mama (i j : ℕ) : a i ∣ a (i * j) := by
  have h₁ : ∀ m n : ℕ, a (m + n + 1) = a m * a n + a (m + 1) * a (n + 1) := by
    intro m
    induction m with
    | zero =>
      intro n
      induction n with
      | zero => simp [a]
      | succ n ih =>
        simp_all [a, Nat.succ_eq_add_one, add_assoc]
        <;> ring_nf at *
        <;> nlinarith
    | succ m ih =>
      intro n
      induction n with
      | zero =>
        simp_all [a]
        <;> ring_nf at *
        <;> nlinarith
      | succ n ih' =>
        have h₂ := ih (n + 1)
        have h₃ := ih n
        have h₄ := ih' 
        have h₅ := ih (n + 2)
        simp [a, Nat.succ_eq_add_one, add_assoc] at *
        <;> ring_nf at *
        <;> nlinarith
  
  have h₂ : a i ∣ a (i * j) := by
    have h₃ : ∀ i j : ℕ, a i ∣ a (i * j) := by
      intro i j
      have h₄ : a i ∣ a (i * j) := by
        induction' j with j ih
        · -- Base case: j = 0
          simp [a]
          <;>
          exact ⟨0, by simp [a]⟩
        · -- Inductive step: assume the statement holds for j, prove for j + 1
          have h₅ : a (i * (j + 1)) = a (i * j + i) := by
            ring_nf
          rw [h₅]
          by_cases ja : i = 0
          · subst i; simp [a]
          by_cases jb : j = 0
          · subst j; simp [a]
          have fc : 1 ≤ i * j := by clear * - ja jb; (have d1 : 1 ≤ i := by omega); (have d2 : 1 ≤ j := by omega); nlinarith
          have h₆ : a (i * j + i) = a ((i * j - 1) + (i + 1)) := by
            rw [(by omega : i * j + i = (i * j - 1) + (i + 1))]
          rw [h₆]
          have h₇ : a ((i * j - 1) + (i + 1)) = a ((i * j - 1) + i + 1) := by
            ring_nf
          rw [h₇]
          have h₈ : a ((i * j - 1) + i + 1) = a (i * j - 1) * a i + a (i * j - 1 + 1) * a (i + 1) := by
            have h₉ := h₁ (i * j - 1) i
            have h₁₀ := h₁ (i * j - 1) 0
            have h₁₁ := h₁ 0 (i * j - 1)
            have h₁₂ := h₁ i 0
            have h₁₃ := h₁ 0 i
            cases i with
            | zero =>
              simp [a] at *
              <;> ring_nf at *
              <;> simp_all [a]
              <;> ring_nf at *
              <;> omega
            | succ i' =>
              cases j with
              | zero =>
                simp [a, Nat.mul_succ, Nat.add_assoc] at *
                <;> ring_nf at *
                <;> simp_all [a]
                <;> ring_nf at *
                <;> omega
              | succ j' =>
                simp [a, Nat.mul_succ, Nat.add_assoc, Nat.add_sub_assoc, Nat.add_sub_cancel] at *
                <;> ring_nf at *
                <;> simp_all [a]
                <;> ring_nf at *
                <;> omega
          rw [h₈]
          have h₉ : a i ∣ a (i * j - 1) * a i := by
            exact ⟨a (i * j - 1), by ring⟩
          have h₁₀ : a i ∣ a (i * j - 1 + 1) * a (i + 1) := by
            have h₁₁ : a i ∣ a (i * j) := ih
            have h₁₂ : a i ∣ a (i * j - 1 + 1) * a (i + 1) := by
              by_cases h : i = 0
              · -- Case i = 0
                subst h
                simp [a] at *
                <;> ring_nf at *
                <;> simp_all [a]
                <;> ring_nf at *
                <;> omega
              · -- Case i ≠ 0
                have h₁₃ : i > 0 := Nat.pos_of_ne_zero h
                have h₁₄ : a i ∣ a (i * j) := ih
                have h₁₅ : a i ∣ a (i * j - 1 + 1) * a (i + 1) := by
                  -- Use the fact that a_i divides a_{i * j} and the properties of the sequence
                  -- to show that a_i divides a_{i * j - 1 + 1} * a_{i + 1}
                  cases j with
                  | zero =>
                    simp [a, Nat.mul_succ, Nat.add_assoc] at *
                    <;> ring_nf at *
                    <;> simp_all [a]
                    <;> ring_nf at *
                    <;> omega
                  | succ j' =>
                    cases i with
                    | zero =>
                      simp_all [a]
                    | succ i' =>
                      simp [a, Nat.mul_succ, Nat.add_assoc, Nat.add_sub_assoc, Nat.add_sub_cancel] at *
                      <;> ring_nf at *
                      <;> simp_all [a]
                      <;> ring_nf at *
                      rw [mul_assoc, ← mul_add]
                      exact Dvd.dvd.mul_right ih (a (1 + i') * 4 + a i')
                exact h₁₅
            exact h₁₂
          have h₁₁ : a i ∣ a (i * j - 1) * a i + a (i * j - 1 + 1) * a (i + 1) := by
            exact dvd_add h₉ h₁₀
          exact h₁₁
      exact h₄
    exact h₃ i j
  
  exact h₂

lemma idx (n k : ℕ) :
    a (n + k + 1) = a (k + 1) * a (n + 1) + a k * a n := by
  have h_base_case_n_eq_zero : ∀ (k : ℕ), a (0 + k + 1) = a (k + 1) * a (0 + 1) + a k * a 0 := by
    intro k
    have h₁ : a (0 + k + 1) = a (k + 1) := by simp [Nat.add_assoc]
    have h₂ : a (k + 1) * a (0 + 1) + a k * a 0 = a (k + 1) * a 1 + a k * a 0 := by simp [Nat.add_assoc]
    have h₃ : a (k + 1) * a 1 + a k * a 0 = a (k + 1) * 1 + a k * 0 := by
      simp [a]
    have h₄ : a (k + 1) * 1 + a k * 0 = a (k + 1) := by simp
    have h₅ : a (0 + k + 1) = a (k + 1) * a (0 + 1) + a k * a 0 := by
      simp [h₁, h₂, h₃, h₄, a]
      <;> ring
      <;> simp_all [a]
      <;> ring
    exact h₅
  
  have h_base_case_n_eq_one : ∀ (k : ℕ), a (1 + k + 1) = a (k + 1) * a (1 + 1) + a k * a 1 := by
    intro k
    have h₁ : a (1 + k + 1) = a (k + 2) := by
      simp [Nat.add_assoc]
      <;> ring_nf
    have h₂ : a (k + 2) = 4 * a (k + 1) + a k := by
      have h₃ : ∀ n, a (n + 2) = 4 * a (n + 1) + a n := by
        intro n
        induction n with
        | zero => simp [a] <;> norm_num
        | succ n ih =>
          simp_all [a, Nat.add_assoc, Nat.add_right_comm]
          <;> ring_nf at *
          <;> omega
      have h₄ := h₃ k
      exact h₄
    have h₃ : a (k + 1) * a (1 + 1) + a k * a 1 = a (k + 1) * 4 + a k * 1 := by
      have h₄ : a (1 + 1) = 4 := by
        norm_num [a]
      have h₅ : a 1 = 1 := by
        norm_num [a]
      rw [h₄, h₅]
      <;> ring
    have h₄ : a (k + 1) * 4 + a k * 1 = 4 * a (k + 1) + a k := by
      ring
    have h₅ : a (1 + k + 1) = a (k + 1) * a (1 + 1) + a k * a 1 := by
      rw [h₁, h₂, h₃, h₄]
      <;> ring_nf
      <;> omega
    exact h₅
  
  have h_inductive_step : ∀ (n : ℕ), (∀ (k : ℕ), a (n + k + 1) = a (k + 1) * a (n + 1) + a k * a n) → (∀ (k : ℕ), a ((n + 1) + k + 1) = a (k + 1) * a ((n + 1) + 1) + a k * a (n + 1)) → (∀ (k : ℕ), a ((n + 2) + k + 1) = a (k + 1) * a ((n + 2) + 1) + a k * a (n + 2)) := by
    intro n h₁ h₂
    intro k
    have h₃ : a ((n + 2) + k + 1) = 4 * a ((n + 1) + k + 1) + a (n + k + 1) := by
      have h₄ : (n + 2) + k + 1 = (n + k + 1) + 2 := by
        ring
      rw [h₄]
      have h₅ : a ((n + k + 1) + 2) = 4 * a ((n + k + 1) + 1) + a (n + k + 1) := by
        have h₆ : ∀ m, a (m + 2) = 4 * a (m + 1) + a m := by
          intro m
          induction m with
          | zero => simp [a]
          | succ m ih =>
            simp_all [a]
            <;> ring_nf at *
            <;> omega
        have h₇ := h₆ (n + k + 1)
        have h₈ := h₆ (n + k)
        have h₉ := h₆ (n + k + 2)
        simp [a, Nat.add_assoc, Nat.add_right_comm] at h₇ h₈ h₉ ⊢
        <;> ring_nf at *
        <;> omega
      have h₆ : (n + k + 1) + 1 = (n + 1) + k + 1 := by ring
      rw [h₆] at h₅
      exact h₅
    have h₄ : a ((n + 1) + k + 1) = a (k + 1) * a ((n + 1) + 1) + a k * a (n + 1) := h₂ k
    have h₅ : a (n + k + 1) = a (k + 1) * a (n + 1) + a k * a n := h₁ k
    have h₆ : a ((n + 2) + k + 1) = 4 * (a (k + 1) * a ((n + 1) + 1) + a k * a (n + 1)) + (a (k + 1) * a (n + 1) + a k * a n) := by
      rw [h₃, h₄, h₅]
      <;> ring_nf
      <;> simp [a, Nat.add_assoc, Nat.add_right_comm]
      <;> ring_nf
      <;> omega
    have h₇ : a (k + 1) * a ((n + 2) + 1) + a k * a (n + 2) = 4 * (a (k + 1) * a ((n + 1) + 1) + a k * a (n + 1)) + (a (k + 1) * a (n + 1) + a k * a n) := by
      have h₈ : a ((n + 2) + 1) = 4 * a ((n + 1) + 1) + a (n + 1) := by
        have h₉ : a ((n + 2) + 1) = a ((n + 1) + 2) := by
          ring_nf
        rw [h₉]
        have h₁₀ : a ((n + 1) + 2) = 4 * a ((n + 1) + 1) + a (n + 1) := by
          have h₁₁ : ∀ m, a (m + 2) = 4 * a (m + 1) + a m := by
            intro m
            induction m with
            | zero => simp [a]
            | succ m ih =>
              simp_all [a]
              <;> ring_nf at *
              <;> omega
          have h₁₂ := h₁₁ (n + 1)
          simp [Nat.add_assoc, Nat.add_right_comm] at h₁₂ ⊢
          <;> ring_nf at *
          <;> omega
        rw [h₁₀]
        <;> ring_nf
      have h₉ : a (n + 2) = 4 * a (n + 1) + a n := by
        have h₁₀ : ∀ m, a (m + 2) = 4 * a (m + 1) + a m := by
          intro m
          induction m with
          | zero => simp [a]
          | succ m ih =>
            simp_all [a]
            <;> ring_nf at *
            <;> omega
        have h₁₁ := h₁₀ n
        simp [Nat.add_assoc, Nat.add_right_comm] at h₁₁ ⊢
        <;> ring_nf at *
        <;> omega
      calc
        a (k + 1) * a ((n + 2) + 1) + a k * a (n + 2) = a (k + 1) * (4 * a ((n + 1) + 1) + a (n + 1)) + a k * (4 * a (n + 1) + a n) := by
          rw [h₈, h₉]
          <;> ring_nf
        _ = 4 * (a (k + 1) * a ((n + 1) + 1)) + a (k + 1) * a (n + 1) + (a k * (4 * a (n + 1)) + a k * a n) := by
          ring_nf
        _ = 4 * (a (k + 1) * a ((n + 1) + 1)) + a (k + 1) * a (n + 1) + 4 * (a k * a (n + 1)) + a k * a n := by
          ring_nf
        _ = 4 * (a (k + 1) * a ((n + 1) + 1) + a k * a (n + 1)) + (a (k + 1) * a (n + 1) + a k * a n) := by
          ring_nf
        _ = 4 * (a (k + 1) * a ((n + 1) + 1) + a k * a (n + 1)) + (a (k + 1) * a (n + 1) + a k * a n) := by rfl
        _ = 4 * (a (k + 1) * a ((n + 1) + 1) + a k * a (n + 1)) + (a (k + 1) * a (n + 1) + a k * a n) := by rfl
    have h₈ : a ((n + 2) + k + 1) = a (k + 1) * a ((n + 2) + 1) + a k * a (n + 2) := by
      linarith
    exact h₈
  
  have h_main : a (n + k + 1) = a (k + 1) * a (n + 1) + a k * a n := by
    have h₁ : ∀ (n k : ℕ), a (n + k + 1) = a (k + 1) * a (n + 1) + a k * a n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro k
        match n with
        | 0 =>
          have h₂ := h_base_case_n_eq_zero k
          simpa using h₂
        | 1 =>
          have h₃ := h_base_case_n_eq_one k
          simpa using h₃
        | n + 2 =>
          have h₄ := ih (n + 1) (by omega)
          have h₅ := ih (n) (by omega)
          have h₆ := h_inductive_step n h₅ h₄ k
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₆
    exact h₁ n k
  exact h_main

lemma yw : ∀ n, Nat.gcd (a n) (a (n+1)) = 1 := by
  have h0 : ∀ n, a (n + 2) = 4 * a (n + 1) + a n := by simp [a]
  have h3 : a 0 = 0 := by simp [a]
  have h4 : a 1 = 1 := by simp [a]
  have h_base : Nat.gcd (a 0) (a 1) = 1 := by
    rw [h3, h4]
    <;> norm_num
  
  have h_inductive_step : ∀ n, Nat.gcd (a n) (a (n + 1)) = 1 → Nat.gcd (a (n + 1)) (a (n + 2)) = 1 := by
    intro n hn
    have h₁ : a (n + 2) = 4 * a (n + 1) + a n := h0 n
    have h₂ : Nat.gcd (a (n + 1)) (a (n + 2)) = Nat.gcd (a (n + 1)) (4 * a (n + 1) + a n) := by
      rw [h₁]
    rw [h₂]
    have h₃ : Nat.gcd (a (n + 1)) (4 * a (n + 1) + a n) = Nat.gcd (a (n + 1)) (a n) := by
      -- Prove that gcd(a_{n+1}, 4a_{n+1} + a_n) = gcd(a_{n+1}, a_n)
      have h₄ : Nat.gcd (a (n + 1)) (4 * a (n + 1) + a n) = Nat.gcd (a (n + 1)) (a n) := by
        -- Use the property of gcd: gcd(a, b) = gcd(a, b - ka)
        rw [show 4 * a (n + 1) + a n = a n + 4 * a (n + 1) by ring]
        -- Apply the Euclidean algorithm step
        simpa [Nat.gcd_comm, Nat.gcd_add_mul_right_right, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using Nat.gcd_comm (a (n + 1)) (a n + 4 * a (n + 1))
      rw [h₄]
    rw [h₃]
    -- Prove that gcd(a_{n+1}, a_n) = 1 using the induction hypothesis
    have h₄ : Nat.gcd (a (n + 1)) (a n) = Nat.gcd (a n) (a (n + 1)) := by
      rw [Nat.gcd_comm]
    rw [h₄]
    rw [hn]
  
  have h_main : ∀ n, Nat.gcd (a n) (a (n + 1)) = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      match n with
      | 0 =>
        -- Base case: when n = 0, use the base case property.
        exact h_base
      | 1 =>
        -- For n = 1, apply the inductive step to n = 0.
        have h₁ : Nat.gcd (a 0) (a 1) = 1 := h_base
        have h₂ : Nat.gcd (a 1) (a 2) = 1 := h_inductive_step 0 h₁
        have h₃ : a 2 = 4 * a 1 + a 0 := h0 0
        have h₄ : a 0 = 0 := h3
        have h₅ : a 1 = 1 := h4
        have h₆ : a 2 = 4 * 1 + 0 := by
          rw [h₃, h₄, h₅]
          <;> ring
        have h₇ : a 2 = 4 := by
          rw [h₆]
          <;> norm_num
        -- Simplify the gcd expression for n = 1.
        simpa [h₄, h₅, h₇, Nat.gcd_comm] using h₂
      | n + 2 =>
        -- For n ≥ 2, use the inductive hypothesis.
        have h₁ : Nat.gcd (a (n + 1)) (a (n + 2)) = 1 := by
          simp [h0, h3, h4, h_inductive_step (n + 1) (ih (n + 1) (by omega))]
          rw [Nat.gcd_comm]; apply ih; clear * -; omega
        have h₂ : Nat.gcd (a (n + 2)) (a ((n + 2) + 1)) = 1 := by
          simp [h0, h3, h4, h_inductive_step (n + 2) (by simp [h0, h3, h4]; apply ih; omega)]
          apply ih; omega
        simpa [Nat.gcd_comm, Nat.add_assoc] using h₂
  exact h_main

lemma ls n q : Nat.gcd (a (q * n + 1)) (a n) = 1 := by
  induction q with
  | zero => simp [a]
  | succ q ih =>
    have dj := yw
    have db := mama
    have yy := idx
    have c0 : a 0 = 0 := by decide
    have c1 : a 1 = 1 := by decide
    have c2 : ∀ n, a (n + 2) = 4 * a (n + 1) + a n := by simp [a]
    have fd := yy (n * q) n
    rw [(by ring : (q + 1) * n + 1 = n * q + n + 1)]
    simp [fd, a]
    rw [backport.gcd_mul_right_left_of_gcd_eq_one (by rw [Nat.gcd_comm]; apply dj)]
    rw [Nat.mul_comm, ih]

lemma jxak {m k : ℕ} (n : ℕ) : m ∣ k → (n + k).gcd m = n.gcd m := by
  intro mk
  obtain ⟨q, hk⟩ := mk
  rw [hk]
  simp [Nat.gcd_add_mul_self]

def gghu0 (m n) (jr : n < m) : Nat.gcd (a m) (a n) = a (Nat.gcd m n) := by
  by_cases ym : m = 0
  · subst m; simp [a]
  by_cases yn : n = 0
  · subst n; simp [a]
  have ex : m = n * (m / n) + m % n := by rw [Nat.div_add_mod m n]
  rw [ex]
  by_cases yu : m % n = 0
  · simp [yu] at *
    clear yu
    have cj := mama n (m / n)
    simp [Nat.gcd_eq_right cj]
  -- now we apply the idx lemma
  have dj := idx (n * (m / n)) (m % n - 1)
  rw [(by omega : n * (m / n) + (m % n - 1) + 1  = n * (m / n) + m % n), (by omega : (m % n - 1 + 1) = m % n)] at dj
  rw [dj]
  have st1 (n m : ℕ) (h₀ : n ≠ 0) (h₁ : m ≠ 0) :
    Nat.gcd (n * (m / n) + m % n) n = Nat.gcd (m % n) n := by 
    simp [Nat.gcd_add_mul_self, Nat.add_comm]
  rw [st1 _ _ yn ym]
  -- make right term disappear
  have cj := mama n (m / n)
  rw [jxak _ (by exact backport.dvd_mul_left_of_dvd cj (a (m % n - 1)))]
  have rr := ls n (m / n)
  rw [mul_comm] at rr
  rw [mul_comm, backport.gcd_mul_right_left_of_gcd_eq_one rr]
  conv => left; rw [Nat.gcd_comm]
  conv => right; rw [Nat.gcd_comm]
  apply gghu0
  apply Nat.mod_lt; omega

termination_by m + n
decreasing_by
  have dja := Nat.mod_le m n
  obtain jj | jj := eq_or_lt_of_le dja
  · rw [Nat.mod_eq_iff_lt] at jj
    have aj := @Nat.mod_lt m n (by omega)
    all_goals omega
  · omega

theorem number_theory_26417 : Nat.gcd (a 1986) (a 6891) = 17 := by
  rw [Nat.gcd_comm, gghu0 _ _ (by decide)]
  rw [(by decide : (Nat.gcd 6891 1986) = 3)]
  -- we arrive at a 3 = 17, this is trivial, just decide
  decide