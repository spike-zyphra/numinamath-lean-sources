import Mathlib
set_option maxHeartbeats 99999999999999999999999999999999999999999999999999999999999999999999999999999999
def isGood (n : ℕ) := ∀ d, d ∣ n → (Nat.digits 2 d).sum ≤ 2

lemma pref (x b : ℕ) (ha : 0 < b + 1) (rt : 1 + 2 ^ (b + 1) * 2 + 2 ^ ((b + 1) * 2) = 2 ^ x) : False := by 
  have h1 : b ≥ 0 := by 
    omega
  have h2 : 1 + 2 ^ (b + 1) * 2 + 2 ^ ((b + 1) * 2) = 1 + 2 ^ (b + 2) + 2 ^ (2 * b + 2) := by 
    ring_nf
    <;> omega
  rw [h2] at rt
  have h3 : x > 0 := by 
    by_contra h
    push_neg at h
    have h4 : x = 0 := by 
      omega
    rw [h4] at rt
    have h5 : 2 ^ (b + 2) > 0 := by 
      apply Nat.pos_pow_of_pos
      omega
    have h6 : 2 ^ (2 * b + 2) > 0 := by 
      apply Nat.pos_pow_of_pos
      omega
    have h7 : 1 + 2 ^ (b + 2) + 2 ^ (2 * b + 2) > 1 := by 
      omega
    linarith
  have h4 : x ≥ 1 := by omega
  have h5 : (2 : ℕ) ^ x % 2 = 0 := by 
    have h6 : x ≥ 1 := by omega
    have h7 : ∀ k : ℕ, (2 : ℕ) ^ (k + 1) % 2 = 0 := by 
      intro k 
      induction k with 
      | zero => 
        norm_num 
      | succ k ih => 
        simp [pow_succ, pow_zero, Nat.mul_mod, Nat.add_mod] at ih ⊢ 
        <;> omega 
    specialize h7 (x - 1)
    have : x = (x - 1) + 1 := by 
      omega 
    rw [this] 
    apply h7 
  have h6 : (1 + 2 ^ (b + 2) + 2 ^ (2 * b + 2) : ℕ) % 2 = 1 := by 
    have h7 : (2 ^ (b + 2) : ℕ) % 2 = 0 := by 
      have h8 : ∀ k : ℕ, (2 ^ (k + 2) : ℕ) % 2 = 0 := by 
        intro k 
        induction k with 
        | zero => 
          norm_num 
        | succ k ih => 
          simp [pow_succ, pow_zero, Nat.mul_mod, Nat.add_mod] at ih ⊢ 
          <;> omega 
      specialize h8 b 
      exact h8 
    have h8 : (2 ^ (2 * b + 2) : ℕ) % 2 = 0 := by 
      have h9 : ∀ k : ℕ, (2 ^ (2 * k + 2) : ℕ) % 2 = 0 := by 
        intro k 
        induction k with 
        | zero => 
          norm_num 
        | succ k ih => 
          simp [pow_succ, pow_zero, Nat.mul_mod, Nat.add_mod] at ih ⊢ 
          <;> omega 
      specialize h9 b 
      exact h9 
    omega 
  have h7 : (2 ^ x : ℕ) % 2 = 0 := h5 
  have h8 : (1 + 2 ^ (b + 2) + 2 ^ (2 * b + 2) : ℕ) % 2 = (2 ^ x : ℕ) % 2 := by 
    omega 
  rw [h6, h7] at h8 
  all_goals omega

lemma ufjsj (x d : ℕ) (hdp : Nat.Prime d) (hdpx : d ∣ x) (hdd : 3 ≤ d) (ex : ∃ i, d = 2 ^ i) : False := by
  rcases ex with ⟨i, rfl⟩
  by_cases h : i ≤ 1
  · -- i ≤ 1
    interval_cases i <;> norm_num at hdp hdd
    all_goals linarith
  · -- i > 1
    have h2 : i ≥ 2 := by omega
    have h3 : ¬ Nat.Prime (2 ^ i) := by
      have h4 : i ≥ 2 := h2
      have h7 : (2 : ℕ) ^ i = 2 * (2 ^ (i - 1)) := by
        cases i with
        | zero => linarith
        | succ i =>
          cases i with
          | zero => linarith
          | succ i =>
            simp [Nat.pow_succ, Nat.mul_assoc]
            <;> ring_nf <;> omega
      have h8 : 1 < 2 := by norm_num
      have h9 : 1 < 2 ^ (i - 1) := by
        have h10 : i - 1 ≥ 1 := by omega
        have h11 : 2 ^ (i - 1) ≥ 2 ^ 1 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals linarith
        have h12 : 2 ^ 1 = 2 := by norm_num
        have h13 : 2 ^ (i - 1) ≥ 2 := by
          linarith [h12, h11]
        linarith
      have h14 : ¬ Nat.Prime (2 ^ i) := by
        rw [h7]
        apply Nat.not_prime_mul (by linarith) (by linarith)
      exact h14
    have h4 : Nat.Prime (2 ^ i) := hdp
    contradiction

lemma one (d : ℕ) (dls : (Nat.digits 2 d).sum = 1) : ∃ i, d = 2 ^ i := by
  induction' d using Nat.strongInductionOn with dke kds
  by_cases uuu : dke = 0
  · subst dke; exfalso; revert dls; native_decide
  have := kds (dke / 2) (by omega)
  rw [Nat.digits_eq_cons_digits_div (by decide) (by tauto)] at dls
  obtain yy | yy : dke % 2 = 0 ∨ dke % 2 = 1 := by clear * -; omega
  · simp [yy] at dls
    obtain ⟨yz, uh⟩ := kds (dke / 2) (by omega) dls
    exists (yz + 1)
    simp [Nat.pow_add]; omega
  simp [yy] at dls
  clear * - yy dls
  rw [List.sum_eq_zero_iff] at dls
  have jcks := Nat.getLast_digit_ne_zero 2 (m := dke / 2)
  have jdk : dke / 2 = 0 := by
    by_contra! jd
    have := jcks jd
    revert this; simp
    apply dls; simp
  clear * - yy jdk
  exists 0; simp; omega

lemma carve (x : ℕ) (hx : x < 2012) (prdf : ∀ (d : ℕ), Nat.Prime d → d ∣ x → 3 ≤ d → ∃ i, 0 < i ∧ d = 2 ^ i + 1)
  (al : ¬x = 0) (prms : ∀ (d : ℕ), Nat.Prime d → d ∣ x → d ∈ ({2, 3, 5, 17, 257} : Set ℕ))
  (vv : ∀ (d : ℕ), d ∣ x → (∃ a b, a < b ∧ d = 2 ^ a + 2 ^ b) ∨ ∃ x, d = 2 ^ x)
  (work : ∀ (a b : ℕ), 0 < a → 0 < b → (2 ^ a + 1) * (2 ^ b + 1) ∣ x → a = 1 ∧ b = 1) (w : ℕ)
  (dh : ∀ (b : ℕ), Nat.Prime b → b ∣ w → b ≠ 2) (ww : ∀ (b : ℕ), Nat.Prime b → b ∣ x → b ∣ w ∨ b = 2)
  (trs : ∀ (b : ℕ), b ∣ w → b ∣ x) (uu : ¬w = 1) (tt : ℕ) (cr : w ∣ x) (un : ¬tt = 1) (nv : tt ∣ w) (mv : w = 3 * tt)
  (ti : 3 ∣ tt) : w = 3 ∨ w = 5 ∨ w = 9 ∨ w = 17 ∨ w = 257 := by
  right; right; left
  obtain ⟨rr, rfl⟩ := ti
  subst w
  simp at *
  ring_nf at *
  simp at *
  clear un uu nv
  -- now we assume rr has a prime factor
  by_contra! pr
  obtain ⟨pp, hh, ii⟩ := Nat.exists_prime_and_dvd pr
  have cqq := prms pp hh (dvd_trans (dvd_trans ii (by simp : rr ∣ rr * 9)) cr)
  have qcc := dh pp hh (dvd_trans ii (by simp : rr ∣ rr * 9))
  simp [qcc] at cqq
  have tg := vv (9 * pp) (by {
    obtain ⟨ii, rfl⟩ := ii
    obtain ⟨cr, rfl⟩ := cr
    exists ii * cr
    ring
  })
  clear * - cqq tg
  have si : pp ∈ ({3,5,17,257}: Finset ℕ) := by simp; exact cqq
  obtain tg | tg := tg
  · obtain ⟨a, b, ha, hn⟩ := tg
    apply_fun (fun x => (Nat.digits 2 x).sum) at hn
    have iu : 2 ^ a + 2 ^ b = 2^a * (1 + 2^(b - a)) := by
      ring_nf
      rw [← Nat.pow_add, (by omega : a + (b - a) = b)]
    rw [iu, Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate] at hn
    conv at hn =>
      right; rw [Nat.digits_eq_cons_digits_div (by decide) (by norm_num)]
      rw [(by omega : (b - a) = (b - a - 1) + 1), Nat.pow_succ]
      simp
      rw [(by omega : (1 + 2 ^ (b - a - 1) * 2) / 2 = 2^(b - a - 1) * 1), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate]
      simp
    clear * - hn si
    revert hn; revert si; revert pp; native_decide
  · obtain ⟨x, tg⟩ := tg
    apply_fun (fun x => (Nat.digits 2 x).sum) at tg
    conv at tg =>
      right
      rw [(by norm_num : 2^x = 2^x * 1), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate]
      norm_num
    clear * - si tg
    revert tg; revert si; revert pp; native_decide

/- # Problem:
 3. [6] Find the largest integer less than 2012 all of whose divisors have at most two 1's in their binary representations.
Answer: 1536 Call a number good if all of its positive divisors have at most two 1's in their binary representations. Then, if $p$ is an odd prime divisor of a good number, $p$ must be of the form $2^{k}+1$. The only such primes less than 2012 are $3,5,17$, and 257 , so the only possible prime divisors of $n$ are $2,3,5,17$, and 257 . Next, note that since $\left(2^{i}+1\right)\left(2^{j}+1\right)=2^{i+j}+2^{i}+2^{j}+1$, if either $i$ or $j$ is greater than 1 , then there will be at least 31 's in the binary representation of $\left(2^{i}+1\right)\left(2^{j}+1\right)$, so $\left(2^{i}+1\right)\left(2^{j}+1\right)$ cannot divide a good number. On the other hand, if $i=j=1$, then $\left(2^{1}+1\right)\left(2^{1}+1\right)=9=2^{3}+1$, so 9 is a good number and can divide a good number. Finally, note that since multiplication by 2 in binary just appends additional 0s, so if $n$ is a good number, then $2 n$ is also a good number. It therefore follows that any good number less than 2012 must be of the form $c \cdot 2^{k}$, where $c$ belongs to $\{1,3,5,9,17,257\}$ (and moreover, all such numbers are good). It is then straightforward to check that the largest such number is $1536=3 \cdot 2^{9}$. -/
theorem number_theory_161842 :
    IsGreatest {n | n < 2012 ∧ isGood n} 1536 := by
  constructor
  · simp [isGood]
    intro d
    rw [(by simp : d ∣ 1536 ↔ d ∈ Nat.divisors 1536)]
    revert d; native_decide -- 1536 doesn't have many divisors
  -- now we prove it is the maximum
  simp [isGood, mem_upperBounds]
  intros x hx hd
  have prdf : ∀ d, Nat.Prime d → d ∣ x → 3 ≤ d → ∃ i, 0 < i ∧ d = 2^i + 1 := by
    intro d hdp hdpx hdd
    have kdk := hd d hdpx
    clear hx hd
    have subtask : (Nat.digits 2 d).sum = 2 := by
      by_contra! kds
      obtain dls | dls : (Nat.digits 2 d).sum = 0 ∨ (Nat.digits 2 d).sum = 1 := by omega
      · have := List.sum_eq_zero_iff.mp dls
        clear kdk kds dls hdp hdpx
        have kdls := (Nat.digits_eq_nil_iff_eq_zero (n := d) (b := 2)).mp (by {
          -- have jjj : d ≠ 0 := by linarith
          clear hdd
          induction' d using Nat.strongInductionOn with dke kds
          by_cases kkkk : dke = 0
          · subst dke; simp
          have rcc : dke = 2 * (dke / 2) + (dke % 2) := by omega
          have uns : ∃ ll ee, ee < 2 ∧ dke = 2 * ll + ee := by
            exists (dke / 2), (dke % 2)
            omega
          obtain ⟨ll, ee, oo, uuu⟩ := uns
          clear rcc
          subst dke
          have ioj := kds ll (by omega) (by {
            rw [Nat.digits_eq_cons_digits_div] at this
            rw [(by omega : (2 * ll + ee) % 2 = ee), (by omega : (2 * ll + ee) / 2 = ll)] at this
            simp at this
            tauto; decide; tauto
          })
          rw [Nat.digits_eq_nil_iff_eq_zero] at ioj
          subst ll; simp at *
          have lll : ee = 1 := by omega
          subst ee; simp at *
        })
        subst d; revert hdd; decide
      clear kdk kds
      have ex : ∃ i, d = 2^i := by
        clear * - dls
        apply one d dls
      clear dls
      -- now we refute this
      apply ufjsj x d hdp hdpx hdd ex
    clear kdk
    rw [Nat.digits_eq_cons_digits_div (by decide) (by omega)] at subtask
    have ti : d % 2 = 1 := by
      have kk : d = 2 ∨ Odd d := by exact Nat.Prime.eq_two_or_odd' hdp
      obtain rfl | ooo := kk
      exfalso; revert hdd; decide
      exact Nat.odd_iff.mp ooo
    simp [ti] at subtask
    obtain ⟨i,ii⟩ := one (d/2) (by omega)
    exists i+1
    simp [Nat.pow_add]
    omega
  by_cases al : x = 0
  · subst x; decide
  have prms : ∀ d, Nat.Prime d → d ∣ x → d ∈ ({2,3,5,17,257} : Set ℕ) := by
    intro d hr tn
    have ty : d < 2012 := by clear * - tn hx al; have you : x ≠ 0 := al; have uuu : d ≤ x := Nat.le_of_dvd (by omega : 0 < x) tn; linarith
    have yt := hd d tn
    by_cases dh : d = 2
    · subst d; decide
    have you := prdf d hr tn (by {
      have ue : 2 ≤ d := by exact Nat.Prime.two_le hr
      clear * - dh ue; contrapose! dh
      linarith
    })
    clear * - you dh ty hr
    obtain ⟨i,⟨ii,ui⟩⟩ := you
    subst d
    clear dh
    have uh : i ∈ Finset.range 12 := by
      simp; clear hr
      by_contra h
      push_neg at h
      have h1 : i ≥ 12 := by omega
      have h2 : 2 ^ i ≥ 2 ^ 12 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals
          omega
      have h3 : 2 ^ i + 1 ≥ 4097 := by
        have h4 : 2 ^ i ≥ 4096 := by
          have h5 : 2 ^ 12 = 4096 := by norm_num
          linarith [h2, h5]
        omega
      have h4 : 2 ^ i + 1 < 2012 := ty
      linarith
    revert ii hr ty
    revert uh
    revert i
    native_decide -- only 12 possibilities for i
  
  have vv : ∀ d, d ∣ x → (∃ a b, a < b ∧ d = 2^a + 2^b) ∨ (∃ x, d = 2^x) := by
    intro d dvdx
    have n0 : d ≠ 0 := by
      clear * - al dvdx
      intro d; subst d
      obtain ⟨l, dvdx⟩ := dvdx
      norm_num at dvdx
      exact al dvdx
    clear * - hd dvdx n0
    have qq := hd _ dvdx
    clear hd dvdx
    have dik : (Nat.digits 2 d).sum ≠ 0 := by
      intro uy
      rw [List.sum_eq_zero_iff] at uy
      have jcks := Nat.getLast_digit_ne_zero 2 (m := d)
      revert jcks; simp [n0]
      apply uy; simp

    obtain rr | rr : (Nat.digits 2 d).sum = 1 ∨ (Nat.digits 2 d).sum = 2 := by omega
    · right
      exact one _ rr
    clear qq dik
    induction' d using Nat.strongInductionOn with dke kds
    rw [Nat.digits_eq_cons_digits_div (by decide) (by omega)] at rr
    obtain yh | yh : dke % 2 = 0 ∨ dke % 2 = 1 := by clear * -; omega
    · simp [yh] at rr
      have kq := kds (dke / 2) (by omega) (by omega) rr
      obtain ⟨z, ⟨hz1, hz2⟩⟩ | ⟨z, hp⟩ := kq
      pick_goal 2
      right; exists z+1; simp [Nat.pow_add]; omega
      left; exists z+1, hz1+1; omega
    left
    simp [yh] at rr
    obtain ⟨I, think⟩ := one (dke / 2) (by linarith)
    exists 0, I + 1
    simp [Nat.pow_add, ← think]; omega
  clear hd
  -- we ascertain the form of divisors
  have work a b (ha : 0 < a) (hb : 0 < b) (h : (2^a + 1) * (2^b + 1) ∣ x) : a = 1 ∧ b = 1 := by
    have := vv _ h
    clear * - this ha hb
    obtain rt | rt := this
    · obtain ⟨u,v,hu,hv⟩ := rt
      ring_nf at hv
      rw [← Nat.pow_add] at hv
      by_cases hh : a = b
      · subst b
        simp at *
        cases' u with u
        · norm_num at hv
          rw [Nat.pow_add] at hv
          have hi : 2^a * (2 + 2^a) = 2^v := by ring_nf; rw [Nat.pow_mul]; linarith
          clear hv
          apply_fun (fun y => (Nat.digits 2 y).sum) at hi
          rw [(by ring : 2^v = 2^v * 1), Nat.digits_base_pow_mul (by decide) (by norm_num)] at hi
          simp only [le_refl, add_pos_iff, Nat.ofNat_pos, pow_pos, or_self,
            List.sum_append, List.sum_replicate,
            smul_eq_mul, mul_zero, List.sum_cons, zero_add, mul_one] at hi
          by_contra! aa
          rw [Nat.digits_eq_cons_digits_div (by decide) (by norm_num)] at hi
          have xkk : (2 + 2 ^ a) % 2 = 0 := by
            cases' a with a
            · exfalso; revert ha; decide
            rw [Nat.pow_add]; simp
          rw [xkk, List.sum_cons, zero_add] at hi
          obtain _ | _ | a := a
          · exfalso; revert ha; decide
          · revert aa; decide
          simp [Nat.pow_add, (by omega : (2 ^ a * 2 + 1) % 2 = 1)] at hi
          clear ha hb aa xkk
          rw [(by omega : ((2 ^ a * 2 + 1) / 2) = 2^a)] at hi
          cases' v with v
          · revert hu; decide
          rw [Nat.pow_add, (by simp : 2 ^ v * 2 ^ 1 % 2 = 0), (by simp : 2 ^ v * 2 ^ 1 / 2 = 2^v), (by norm_num : 2^a = 2^a * 1), (by norm_num : 2^v = 2^v * 1), Nat.digits_base_pow_mul (by decide) (by norm_num), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate, List.sum_append, List.sum_replicate] at hi
          simp at hi
        cases' v with v
        · norm_num at hu
        conv at hv =>
          right; simp [Nat.pow_add]
        by_contra! bb
        apply_fun (fun x => (Nat.digits 2 x).sum) at hv
        conv at hv =>
          right
          rw [(by ring : 2^u * 2 + 2^v * 2 = 2 * (2^u + 2^v)), Nat.digits_def' (by decide) (by positivity), (by simp : 2 * (2 ^ u + 2 ^ v) % 2 = 0), List.sum_cons, (by simp : 2 * (2 ^ u + 2 ^ v) / 2 = 2 ^ u + 2 ^ v)]
        rw [Nat.zero_add] at hv
        have ff : 2 ^ u + 2 ^ v = 2^u * (1 + 2^(v - u)) := by
          ring_nf
          rw [← Nat.pow_add, (by omega : (u + (v - u)) = v)]
        rw [ff, Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate] at hv
        conv at hv => right; left; norm_num
        conv at hv =>
          right
          rw [Nat.digits_eq_cons_digits_div (by decide) (by norm_num), (by omega : (v - u) = (v - u - 1) + 1)]
          right
          right
          left
          rw [Nat.pow_add]
          simp
        rw [List.sum_cons] at hv
        have yu : (1 + 2 ^ (v - u - 1 + 1)) / 2 = 2 ^ (v - u - 1) := by
          rw [Nat.pow_add]
          norm_num
          clear * -
          omega
        -- solve more
        rw [yu, (by norm_num : 2 ^ (v - u - 1) = 2 ^ (v - u - 1) * 1), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate] at hv
        conv at hv => right; norm_num
        obtain _ | _ | a := a
        · revert ha; decide
        · revert bb; decide
        ring_nf at hv
        -- split digits
        rw [Nat.digits_eq_cons_digits_div (by decide) (by norm_num), (by clear * -; omega : (1 + 2 ^ a * 8 + 2 ^ (a * 2) * 16) % 2 = 1), List.sum_cons, (by clear * -; omega : (1 + 2 ^ a * 8 + 2 ^ (a * 2) * 16) / 2 = 2^a * 4 + 2^(a*2) * 8), Nat.pow_mul, (by ring : (2 ^ a * 4 + (2 ^ a) ^ 2 * 8) = 2^a * (2^2 * (1 + 2 * 2^a))), Nat.digits_base_pow_mul (by decide) (by norm_num), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate, List.sum_append, List.sum_replicate, Nat.digits_eq_cons_digits_div (by decide) (by norm_num), (by clear * -; omega : (1 + 2 * 2 ^ a) % 2 = 1), List.sum_cons] at hv
        norm_num at hv
        rw [(by omega : ((1 + 2 * 2 ^ a) / 2) = 2^a * 1), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate] at hv
        revert hv; norm_num
      wlog hy : a < b
      · have := this b a hb ha u v hu (by rw [← hv]; ring) (by clear * - hh; tauto) (by clear * - hh hy; omega)
        clear * - this; omega
      clear hh
      by_contra! cl
      have uh : b < a + b := by omega
      apply_fun (fun x => (Nat.digits 2 x).sum) at hv
      rw [(by ring_nf; rw [← Nat.pow_add]; rw [(by omega : u + (v - u) = v)] : 2 ^ u + 2 ^ v = 2^u * (1 + 2^(v - u))), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate] at hv
      conv at hv => right; left; norm_num
      conv at hv => right; rw [Nat.digits_eq_cons_digits_div (by decide) (by norm_num)]
      rw [(by omega : v - u = (v - u - 1) + 1), Nat.pow_succ] at hv
      conv at hv => right; right; right; left; simp
      rw [List.sum_cons, (by omega : ((1 + 2 ^ (v - u - 1) * 2) / 2) = 2^(v - u - 1))] at hv
      -- continue solving
      rw [(by norm_num : 2 ^ (v - u - 1)= (2 ^ (v - u - 1)) * 1), Nat.digits_base_pow_mul (by decide) (by norm_num)] at hv
      conv at hv => right; simp
      cases' a with a
      revert ha; decide
      cases' b with b
      revert hb; decide
      rw [Nat.digits_eq_cons_digits_div (by decide) (by norm_num)] at hv
      ring_nf at hv
      simp at hv
      rw [(by omega : (1 + 2 ^ a * 2 + 2 ^ a * 2 ^ b * 4) % 2 = 1)] at hv
      rw [(by omega : ((1 + 2 ^ a * 2 + 2 ^ a * 2 ^ b * 4 + 2 ^ b * 2) / 2) = 2^a + 2^a*2^b*2+2^b)] at hv
      have fagas : 2 ^ a + 2 ^ a * 2 ^ b * 2 + 2 ^ b = 2^a * (1 + 2^b * 2 + 2^(b - a)) := by
        ring_nf
        have kdk : 2 ^ a * 2 ^ (b - a) = 2^b := by
          rw [← Nat.pow_add, (by omega : (a + (b - a)) = b)]
        linarith
      rw [fagas, Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate] at hv
      conv at hv => left; right; left; norm_num
      rw [Nat.digits_eq_cons_digits_div (by decide) (by norm_num)] at hv
      have yj : (1 + 2 ^ b * 2 + 2 ^ (b - a)) % 2 = 1 := by
        rw [(by omega : b - a = (b - a - 1) + 1), Nat.pow_succ]
        simp
      rw [yj, List.sum_cons] at hv
      have nn : ((1 + 2 ^ b * 2 + 2 ^ (b - a)) / 2) = 2^b + 2^(b-a-1) := by
        conv =>
          left
          rw [(by omega : b - a = (b - a - 1) + 1), Nat.pow_succ]
        omega
      rw [nn] at hv
      rw [(by {
        repeat rw [add_comm, ← add_assoc]
        ring_nf
        rw [← Nat.pow_add, ← Nat.pow_succ, (by omega : (b - a - 1 + a).succ = b)]
        ring
      } : 2 ^ b + 2 ^ (b - a - 1) = 2^(b-a-1) * (1 + 2^a * 2)), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate] at hv
      simp at hv
      rw [(by omega : ((1 + 2 ^ a * 2) / 2) = 2^a * 1), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate] at hv
      revert hv; simp
    -- now we still have to solve this simpler case... hopefully it is genuinely simple
    obtain ⟨x, rt⟩ := rt
    ring_nf at rt
    by_cases iu : a = b
    · subst a
      ring_nf at rt
      cases' b with b
      · revert hb; decide
      exfalso
      clear hb
      apply pref x b
      all_goals assumption
    wlog ui : a < b
    · have := this b a hb ha x (by linarith) (by tauto) (by omega)
      clear * - this; tauto
    have fc : b < a + b := by omega
    apply_fun (fun x => (Nat.digits 2 x).sum) at rt
    rw [(by norm_num : 2^x = 2^x * 1), Nat.digits_eq_cons_digits_div (by decide) (by norm_num)] at rt
    cases' a with a
    exfalso; revert ha; decide
    cases' b with b
    exfalso; revert hb; decide
    have ij : (1 + 2 ^ (a + 1) + 2 ^ (a + 1) * 2 ^ (b + 1) + 2 ^ (b + 1)) % 2 = 1 := by
      simp [Nat.pow_succ]
      clear * -
      rw [(by ring : 1 + 2 ^ a * 2 + 2 ^ a * 2 * (2 ^ b * 2) = 1 + 2 * (2^a + 2^a * 2^b * 2))]
      omega
    rw [ij, List.sum_cons] at rt
    conv at rt =>
      left; right; right; right
      simp [Nat.pow_succ]
    rw [(by ring : (1 + 2 ^ a * 2 + 2 ^ a * 2 * (2 ^ b * 2) + 2 ^ b * 2) = 1 + 2 * (2^a + 2^a * 2^b * 2 + 2^b))] at rt
    rw [(by omega : ((1 + 2 * (2 ^ a + 2 ^ a * 2 ^ b * 2 + 2 ^ b)) / 2) = 2 ^ a + 2 ^ a * 2 ^ b * 2 + 2 ^ b), Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append, List.sum_replicate] at rt
    conv at rt => right; simp
    have ls : 2 ^ a + 2 ^ a * 2 ^ b * 2 + 2 ^ b = 2^a * (1 + 2^b * 2 + 2^(b - a)) := by
      ring_nf
      rw [(by rw [Nat.pow_add] : 2 ^ a * 2 ^ (b - a) = 2^(a + (b - a)))]
      rw [(by omega : a + (b - a) = b)]
    rw [ls, Nat.digits_base_pow_mul (by decide) (by norm_num), List.sum_append] at rt
    simp at rt
    rw [(by omega : b - a = (b - a - 1) + 1), Nat.pow_succ] at rt
    omega
  -- with the new hypothesis we can greatly constrain the form of x
  -- WARNING: fully eliminate 2^k prime factor
  have kxs : ∃ k c : ℕ, c ∈ ({1,3,5,9,17,257} : Set ℕ) ∧ x = c * 2^k := by
    exists (Nat.factorization x 2), x / 2^(Nat.factorization x 2)
    have kk := Nat.ord_proj_mul_ord_compl_eq_self x 2
    constructor
    pick_goal 2
    · linarith
    clear kk
    -- we invent a new number w
    obtain ⟨w, hw⟩ : ∃ w, w = x/2^x.factorization 2 := ⟨_, rfl⟩
    -- now we write the real meaning of prime factor of w
    have dh : ∀ b, Nat.Prime b → b ∣ w → b ≠ 2 := by
      intro b hb bb
      subst w
      contrapose! bb
      subst b
      apply Nat.not_dvd_ordCompl
      exact hb
      exact al
    have ww : ∀ b, Nat.Prime b → b ∣ x → (b ∣ w ∨ b = 2) := by
      intro b bb ii
      by_cases jj : b = 2
      · right; exact jj
      simp [jj]
      subst w
      apply Nat.dvd_ordCompl_of_dvd_not_dvd
      exact ii
      clear * - bb jj
      contrapose! jj
      rw [Nat.prime_dvd_prime_iff_eq (by decide) bb] at jj
      rw [jj]
    have trs : ∀ b, b ∣ w → b ∣ x := by
      intro b ub
      subst w
      have uii := Nat.ordCompl_dvd x 2
      exact dvd_trans ub uii
    rw [←hw]; clear hw
    by_cases uu : w = 1
    · subst w; decide
    simp [uu]
    obtain ⟨pp, hh, ii⟩ := Nat.exists_prime_and_dvd uu
    have gh := prms _ hh (trs _ ii)
    simp [dh _ hh ii] at gh
    obtain ⟨tt, mv⟩ := ii
    have cr := trs w (by simp)
    by_cases un : tt = 1
    · subst tt; norm_num at mv; subst w; clear * - gh
      tauto
    obtain ⟨pt, ht, ti⟩ := Nat.exists_prime_and_dvd un
    have uc := dh pt ht (by {
      have nv : tt ∣ w := ⟨pp, by rw[mv];ring⟩
      exact (dvd_trans ti nv)
    })
    have qc := prms pt ht (by {
      have nv : tt ∣ w := ⟨pp, by rw[mv];ring⟩
      exact dvd_trans (dvd_trans ti nv) cr
    })
    simp [uc] at qc
    have nv : tt ∣ w := ⟨pp, by rw[mv];ring⟩
    -- 16 cases ahead!
    obtain rfl | rfl | rfl | rfl := gh
    all_goals obtain rfl | rfl | rfl | rfl := qc
    · apply carve x hx prdf <;> assumption
    · have := work 1 2 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 1 4 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 1 8 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 2 1 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 2 2 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 2 4 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 2 8 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 4 1 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 4 2 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 4 4 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 4 8 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 8 1 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 8 2 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 8 4 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
    · have := work 8 8 (by norm_num) (by decide) (by norm_num; apply dvd_trans _ cr; obtain ⟨ti, rfl⟩ := ti; subst w; ring_nf; simp); exfalso; revert this; decide
  -- finally we find x = 1536
  obtain ⟨k, c, kxs⟩ := kxs
  have clk : k ≤ 10 := by
    rcases kxs with ⟨hc, hx_eq⟩
    by_contra h
    push_neg at h
    have h1 : k ≥ 11 := by omega
    have h2 : (2 : ℕ) ^ 11 ≤ (2 : ℕ) ^ k := by 
      apply Nat.pow_le_pow_right 
      all_goals norm_num 
      all_goals omega 
    have h3 : (2 : ℕ) ^ 11 = 2048 := by norm_num 
    have h4 : (2 : ℕ) ^ 11 ≤ (2 : ℕ) ^ k := h2 
    have h5 : (c : ℕ) ≥ 1 := by
      have hc' : c ∈ ({1, 3, 5, 9, 17, 257} : Set Nat) := hc 
      simp at hc' ⊢
      omega
    have h6 : (c * (2 : ℕ) ^ k) ≥ 2048 := by
      have h7 : (2 : ℕ) ^ k ≥ (2 : ℕ) ^ 11 := h2 
      have h8 : (c : ℕ) ≥ 1 := h5 
      have h9 : (c * (2 : ℕ) ^ k) ≥ (c * (2 : ℕ) ^ 11) := by 
        nlinarith 
      have h10 : (c * (2 : ℕ) ^ 11) ≥ (1 * (2048 : ℕ)) := by
        have h11 : (2 : ℕ) ^ 11 = 2048 := by norm_num 
        have h12 : (c : ℕ) ≥ 1 := h5 
        nlinarith [h11] 
      have h13 : (c * (2 : ℕ) ^ 11) ≥ (2048 : ℕ) := by
        nlinarith 
      linarith [h9, h13]
    have h6' : x ≥ 2048 := by
      linarith [hx_eq, h6]
    linarith
  rcases kxs with ⟨hc, hx_eq⟩
  have cc : c ≤ 257 := by
    clear * - c hc
    have nv : c ∈ ({1, 3, 5, 9, 17, 257} : Finset ℕ) := by simp; simp at hc; exact hc
    revert hc; revert c; decide
  have cd : 1 ≤ c := by
    clear * - c hc
    have nv : c ∈ ({1, 3, 5, 9, 17, 257} : Finset ℕ) := by simp; simp at hc; exact hc
    revert hc; revert c; decide
  cases' k with k
  · norm_num at hx_eq
    linarith
  cases' k with k
  · norm_num at hx_eq
    linarith
  cases' k with k
  · norm_num at hx_eq
    linarith
  cases' k with k
  · norm_num at hx_eq
    have jj : c ≠ 257 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    simp [jj] at hc
    have cc : c ≤ 17 := by
      clear * - c hc
      have nv : c ∈ ({1, 3, 5, 9, 17} : Finset ℕ) := by simp; exact hc
      clear hc; revert c; decide
    linarith
  cases' k with k
  · norm_num at hx_eq
    have jj : c ≠ 257 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    simp [jj] at hc
    have cc : c ≤ 17 := by
      clear * - c hc
      have nv : c ∈ ({1, 3, 5, 9, 17} : Finset ℕ) := by simp; exact hc
      clear hc; revert c; decide
    linarith
  cases' k with k
  · norm_num at hx_eq
    have jj : c ≠ 257 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    simp [jj] at hc
    have cc : c ≤ 17 := by
      clear * - c hc
      have nv : c ∈ ({1, 3, 5, 9, 17} : Finset ℕ) := by simp; exact hc
      clear hc; revert c; decide
    linarith
  cases' k with k
  · norm_num at hx_eq
    have jj : c ≠ 257 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    simp [jj] at hc
    have cc : c ≤ 17 := by
      clear * - c hc
      have nv : c ∈ ({1, 3, 5, 9, 17} : Finset ℕ) := by simp; exact hc
      clear hc; revert c; decide
    linarith
  cases' k with k
  · norm_num at hx_eq
    have jj : c ≠ 257 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have kk : c ≠ 17 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    simp [jj, kk] at hc
    have cc : c ≤ 9 := by
      clear * - c hc
      have nv : c ∈ ({1, 3, 5, 9} : Finset ℕ) := by simp; exact hc
      clear hc; revert c; decide
    linarith
  cases' k with k
  · norm_num at hx_eq
    have jj : c ≠ 257 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have kk : c ≠ 17 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have ll : c ≠ 9 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    simp [jj, kk, ll] at hc
    have cc : c ≤ 5 := by
      clear * - c hc
      have nv : c ∈ ({1, 3, 5} : Finset ℕ) := by simp; exact hc
      clear hc; revert c; decide
    linarith
  cases' k with k
  · norm_num at hx_eq
    have jj : c ≠ 257 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have kk : c ≠ 17 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have ll : c ≠ 9 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have mm : c ≠ 5 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    simp [jj, kk, ll, mm] at hc
    have cc : c ≤ 3 := by
      clear * - c hc
      have nv : c ∈ ({1, 3} : Finset ℕ) := by simp; exact hc
      clear hc; revert c; decide
    linarith
  cases' k with k
  · norm_num at hx_eq
    have jj : c ≠ 257 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have kk : c ≠ 17 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have ll : c ≠ 9 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have mm : c ≠ 5 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    have nn : c ≠ 3 := by
      intro cn
      subst c
      subst x
      exfalso
      revert hx
      decide
    simp [jj, kk, ll, mm, nn] at hc
    have cc : c = 1 := by
      clear * - c hc
      have nv : c ∈ ({1} : Finset ℕ) := by simp; exact hc
      clear hc; revert c; decide
    linarith
  norm_num at clk
  exfalso; clear * - clk; omega