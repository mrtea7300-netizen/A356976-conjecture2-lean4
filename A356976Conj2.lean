/-
Formal proof in pure Lean 4 (zero external dependencies, zero sorrys) of
Zhi-Wei Sun's Conjecture 2 in OEIS A356976 (Nov 16, 2021):

  For every positive integer n, the least positive integer m such that
  f(k) = 2*k^3 + k (k = 1..n) are pairwise distinct modulo m is the least
  power of 2 not smaller than n.

Check with:
  lean conjectures/A356976/A356976Conj2.lean
-/

namespace A356976Conj2

/-- The cubic polynomial f(k) = 2*k^3 + k. -/
def f (k : Nat) : Nat := 2 * k ^ 3 + k

/-- f(1), ..., f(n) are pairwise distinct modulo m. -/
def DistinctMod (n m : Nat) : Prop :=
  ∀ x y, 1 ≤ x → x ≤ n → 1 ≤ y → y ≤ n → f x % m = f y % m → x = y

/-- Elementary primality predicate on Nat. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-! ### Section 1: Pigeonhole Principle & Basic Number Theory -/

theorem pigeonhole : ∀ {a b : Nat}, b < a → ∀ (g : Fin a → Fin b),
    ∃ i j : Fin a, i.val < j.val ∧ g i = g j
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, g => absurd (g ⟨0, Nat.zero_lt_succ _⟩).isLt (Nat.not_lt_zero _)
  | a + 1, b + 1, h, g => by
    let last : Fin (a + 1) := ⟨a, Nat.lt_succ_self a⟩
    by_cases hhit : ∃ i : Fin a, g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = g last
    · obtain ⟨i, hi⟩ := hhit
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, last, i.isLt, hi⟩
    · have hne : ∀ i : Fin a, g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≠ g last := by
        intro i hi; exact hhit ⟨i, hi⟩
      let g' : Fin a → Fin b := fun i =>
        let y := (g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val
        let z := (g last).val
        if hy : y < z then
          ⟨y, by omega⟩
        else
          ⟨y - 1, by
            have hyne : y ≠ z := fun hEq => hne i (Fin.ext hEq)
            have hlt := (g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).isLt
            omega⟩
      have hba : b < a := by omega
      obtain ⟨i, j, hij, hg'⟩ := pigeonhole hba g'
      refine ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, hij, ?_⟩
      apply Fin.ext
      have hi_ne : (g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val ≠ (g last).val :=
        fun hEq => hne i (Fin.ext hEq)
      have hj_ne : (g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩).val ≠ (g last).val :=
        fun hEq => hne j (Fin.ext hEq)
      have hval : (g' i).val = (g' j).val := congrArg Fin.val hg'
      dsimp only [g'] at hval
      by_cases h1 : (g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val < (g last).val <;>
      by_cases h2 : (g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩).val < (g last).val
      · simp only [h1, h2, ↓reduceDIte] at hval; exact hval
      · simp only [h1, h2, ↓reduceDIte] at hval; omega
      · simp only [h1, h2, ↓reduceDIte] at hval; omega
      · simp only [h1, h2, ↓reduceDIte] at hval; omega

theorem pigeonhole_two_maps {a b m : Nat} (hsum : m < a + b)
    (g1 : Fin a → Fin m) (g2 : Fin b → Fin m)
    (hinj1 : ∀ i j, g1 i = g1 j → i = j)
    (hinj2 : ∀ i j, g2 i = g2 j → i = j) :
    ∃ (i : Fin a) (j : Fin b), g1 i = g2 j := by
  let g : Fin (a + b) → Fin m := fun k =>
    if hk : k.val < a then g1 ⟨k.val, hk⟩ else g2 ⟨k.val - a, by omega⟩
  obtain ⟨u, v, huv, hguv⟩ := pigeonhole hsum g
  dsimp only [g] at hguv
  by_cases hu : u.val < a <;> by_cases hv : v.val < a
  · simp only [hu, hv, ↓reduceDIte] at hguv
    have hEq := hinj1 ⟨u.val, hu⟩ ⟨v.val, hv⟩ hguv
    have : u.val = v.val := congrArg (fun x : Fin a => x.val) hEq
    omega
  · simp only [hu, hv, ↓reduceDIte] at hguv
    exact ⟨⟨u.val, hu⟩, ⟨v.val - a, by omega⟩, hguv⟩
  · omega
  · simp only [hu, hv, ↓reduceDIte] at hguv
    have hEq := hinj2 ⟨u.val - a, by omega⟩ ⟨v.val - a, by omega⟩ hguv
    have : u.val - a = v.val - a := congrArg (fun x : Fin b => x.val) hEq
    omega

/-- Bezout's identity for Nat.gcd. -/
theorem exists_bezout : ∀ a b : Nat, ∃ x y : Int, (Nat.gcd a b : Int) = (a : Int) * x + (b : Int) * y
  | 0, b => ⟨0, 1, by simp⟩
  | a + 1, b => by
    have hlt : b % (a + 1) < a + 1 := Nat.mod_lt b (Nat.zero_lt_succ a)
    obtain ⟨x, y, hxy⟩ := exists_bezout (b % (a + 1)) (a + 1)
    have hgcd : Nat.gcd (a + 1) b = Nat.gcd (b % (a + 1)) (a + 1) := by
      rw [Nat.gcd_rec]
    refine ⟨y - ((b / (a + 1) : Nat) : Int) * x, x, ?_⟩
    rw [hgcd, hxy]
    have hdiv : ((b % (a + 1) : Nat) : Int) = (b : Int) - ((a + 1 : Nat) : Int) * ((b / (a + 1) : Nat) : Int) := by
      have := Nat.div_add_mod b (a + 1)
      omega
    rw [hdiv]
    grind
termination_by a _ => a

theorem coprime_of_prime_not_dvd {p a : Nat} (hp : IsPrime p) (hnd : ¬ p ∣ a) :
    Nat.gcd p a = 1 := by
  rcases hp.2 _ (Nat.gcd_dvd_left p a) with h1 | hp'
  · exact h1
  · exfalso; apply hnd; rw [← hp']; exact Nat.gcd_dvd_right p a

theorem dvd_of_coprime_dvd_mul {a b c : Nat} (hcop : Nat.gcd a b = 1) (h : a ∣ b * c) :
    a ∣ c := by
  obtain ⟨x, y, hxy⟩ := exists_bezout a b
  rw [hcop] at hxy
  obtain ⟨k, hk⟩ := h
  have hZ : (c : Int) = (a : Int) * ((c : Int) * x + (k : Int) * y) := by
    have hbc : (b : Int) * (c : Int) = (a : Int) * (k : Int) := by exact_mod_cast hk
    grind
  exact Int.ofNat_dvd.mp ⟨_, hZ⟩

theorem prime_dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · exact Or.inr (dvd_of_coprime_dvd_mul (coprime_of_prime_not_dvd hp ha) h)

theorem dvd_mul_of_coprime {a b n : Nat} (hcop : Nat.gcd a b = 1) (ha : a ∣ n) (hb : b ∣ n) :
    a * b ∣ n := by
  obtain ⟨ka, hka⟩ := ha
  have hb' : b ∣ a * ka := by rw [← hka]; exact hb
  have hcop' : Nat.gcd b a = 1 := by rw [Nat.gcd_comm]; exact hcop
  obtain ⟨kb, hkb⟩ := dvd_of_coprime_dvd_mul hcop' hb'
  exact ⟨kb, by rw [hka, hkb]; grind⟩

theorem coprime_mul_left {a b c : Nat} (ha : Nat.gcd a c = 1) (hb : Nat.gcd b c = 1) :
    Nat.gcd (a * b) c = 1 := by
  obtain ⟨x1, y1, h1⟩ := exists_bezout a c
  obtain ⟨x2, y2, h2⟩ := exists_bezout b c
  rw [ha] at h1; rw [hb] at h2
  have hdvd : ∀ d, d ∣ a * b → d ∣ c → d ∣ 1 := by
    intro d h1d h2d
    obtain ⟨q1, hq1⟩ := h1d
    obtain ⟨q2, hq2⟩ := h2d
    have hZ : (1 : Int) = (d : Int) * ((q1 : Int) * x1 * x2 + (q2 : Int) * ((a : Int) * x1 * y2 + y1 * (b : Int) * x2 + y1 * (c : Int) * y2)) := by
      have hab : (a : Int) * (b : Int) = (d : Int) * (q1 : Int) := by exact_mod_cast hq1
      have hc : (c : Int) = (d : Int) * (q2 : Int) := by exact_mod_cast hq2
      grind
    exact Int.ofNat_dvd.mp ⟨_, hZ⟩
  exact Nat.eq_one_of_dvd_one (hdvd _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))

theorem coprime_pow_left {a b : Nat} (e : Nat) (h : Nat.gcd a b = 1) :
    Nat.gcd (a ^ e) b = 1 := by
  induction e with
  | zero => simp
  | succ k ih => rw [Nat.pow_succ]; exact coprime_mul_left ih h

theorem coprime_pow_right {a b : Nat} (e : Nat) (h : Nat.gcd a b = 1) :
    Nat.gcd a (b ^ e) = 1 := by
  rw [Nat.gcd_comm]; exact coprime_pow_left e (by rw [Nat.gcd_comm]; exact h)

theorem exists_mod_inv {a m : Nat} (hm : 0 < m) (hcop : Nat.gcd a m = 1) :
    ∃ b : Nat, b < m ∧ (a * b) % m = 1 % m := by
  obtain ⟨x, y, hxy⟩ := exists_bezout a m
  rw [hcop] at hxy
  let bInt : Int := x % (m : Int)
  have hb0 : 0 ≤ bInt := Int.emod_nonneg _ (by omega)
  have hblt : bInt < (m : Int) := Int.emod_lt_of_pos _ (by omega)
  refine ⟨bInt.toNat, by omega, ?_⟩
  have hbCast : (bInt.toNat : Int) = bInt := Int.toNat_of_nonneg hb0
  have hmodZ : ((a * bInt.toNat : Nat) : Int) % (m : Int) = (1 : Int) % (m : Int) := by
    push_cast
    rw [hbCast]
    have h1 : ((a : Int) * (x % (m : Int))) % (m : Int) = ((a : Int) * x) % (m : Int) := by
      rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
    rw [h1]
    have h2 : (a : Int) * x = 1 + (m : Int) * (-y) := by grind
    rw [h2, Int.add_mul_emod_self_left]
  exact_mod_cast hmodZ

theorem mod_eq_iff_dvd_sub {a b m : Nat} (hab : a ≤ b) :
    a % m = b % m ↔ m ∣ (b - a) := by
  constructor
  · intro h
    by_cases hm : m = 0
    · subst hm; simp at h; omega
    · have ha := Nat.div_add_mod a m
      have hb := Nat.div_add_mod b m
      have hdiv : a / m ≤ b / m := Nat.div_le_div_right hab
      refine ⟨b / m - a / m, ?_⟩
      have : b - a = m * (b / m) - m * (a / m) := by omega
      rw [this, ← Nat.mul_sub]
  · intro ⟨k, hk⟩
    have hb : b = a + m * k := by omega
    rw [hb, Nat.add_mul_mod_self_left]

/-! ### Section 2: Factorization of f(y) - f(x) and Upper Bound (m = 2^r) -/

theorem f_mono {x y : Nat} (hxy : x ≤ y) : f x ≤ f y := by
  unfold f; have := Nat.pow_le_pow_left hxy 3; omega

theorem f_diff_eq {x y : Nat} (hxy : x ≤ y) :
    f y - f x = (y - x) * (2 * (x ^ 2 + x * y + y ^ 2) + 1) := by
  unfold f
  have hmono : 2 * x ^ 3 + x ≤ 2 * y ^ 3 + y := f_mono hxy
  have hZ : (((2 * y ^ 3 + y) - (2 * x ^ 3 + x) : Nat) : Int) =
            (((y - x) * (2 * (x ^ 2 + x * y + y ^ 2) + 1) : Nat) : Int) := by
    rw [Int.ofNat_sub hmono]
    push_cast
    rw [Int.ofNat_sub hxy]
    grind
  exact Int.ofNat.inj hZ

theorem distinctMod_pow2 (n r : Nat) (hnr : n ≤ 2 ^ r) : DistinctMod n (2 ^ r) := by
  intro x y hx1 hxn hy1 hyn hmod
  suffices hle : ∀ a b, 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n → a ≤ b → f a % 2 ^ r = f b % 2 ^ r → a = b by
    rcases Nat.le_total x y with h | h
    · exact hle x y hx1 hxn hy1 hyn h hmod
    · exact (hle y x hy1 hyn hx1 hxn h hmod.symm).symm
  intro a b ha1 han hb1 hbn hab hEq
  have hdvd : 2 ^ r ∣ f b - f a := (mod_eq_iff_dvd_sub (f_mono hab)).mp hEq
  rw [f_diff_eq hab] at hdvd
  have h2prime : IsPrime 2 := ⟨by omega, fun d hd => by
    have hle2 := Nat.le_of_dvd (by omega) hd
    have hne0 : d ≠ 0 := fun h0 => by rw [h0] at hd; exact absurd hd (by decide)
    omega⟩
  have hcop : Nat.gcd (2 ^ r) (2 * (a ^ 2 + a * b + b ^ 2) + 1) = 1 :=
    coprime_pow_left r (coprime_of_prime_not_dvd h2prime (by omega))
  have hdvd_ba : 2 ^ r ∣ (b - a) := by
    rw [Nat.mul_comm] at hdvd
    exact dvd_of_coprime_dvd_mul hcop hdvd
  have hzero : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_ba (by omega)
  omega

/-! ### Section 3: Case 1 (3 ∣ m) -/

theorem three_dvd_f (k : Nat) : 3 ∣ f k := by
  unfold f
  have h : (2 * k ^ 3 + k) % 3 = 0 := by
    have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    have hpow : k ^ 3 = k * k * k := by simp [Nat.pow_succ, Nat.pow_zero]
    rw [hpow]
    rcases hk with h0 | h1 | h2
    · rw [Nat.add_mod, Nat.mul_mod 2, Nat.mul_mod (k * k), Nat.mul_mod k k, h0]
    · rw [Nat.add_mod, Nat.mul_mod 2, Nat.mul_mod (k * k), Nat.mul_mod k k, h1]
    · rw [Nat.add_mod, Nat.mul_mod 2, Nat.mul_mod (k * k), Nat.mul_mod k k, h2]
  exact Nat.dvd_of_mod_eq_zero h

theorem collision_of_three_dvd {m : Nat} (hm : 3 ∣ m) (hm_pos : 0 < m) :
    ∃ x y, 1 ≤ x ∧ x < y ∧ y ≤ 1 + m / 3 ∧ f x % m = f y % m := by
  have hfac : ∀ n, 0 < n → ∃ e d, n = 3 ^ e * d ∧ ¬ (3 ∣ d) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases h3 : 3 ∣ n
      · obtain ⟨q, hq⟩ := h3
        have hq_pos : 0 < q := by omega
        have hq_lt : q < n := by omega
        obtain ⟨e, d, hed, hnd⟩ := ih q hq_lt hq_pos
        exact ⟨e + 1, d, by rw [hq, hed, Nat.pow_succ]; grind, hnd⟩
      · exact ⟨0, n, by simp, h3⟩
  obtain ⟨e, d, hmed, hnd3⟩ := hfac m hm_pos
  have he1 : 1 ≤ e := by
    cases e with
    | zero => simp at hmed; rw [← hmed] at hnd3; exact absurd hm hnd3
    | succ _ => omega
  have h3e_pos : 0 < 3 ^ (e - 1) := Nat.pow_pos (by omega)
  let g : Fin (3 ^ (e - 1) + 1) → Fin (3 ^ (e - 1)) := fun j =>
    ⟨(f (1 + j.val * d) % 3 ^ e) / 3, by
      have hlt : f (1 + j.val * d) % 3 ^ e < 3 ^ e := Nat.mod_lt _ (Nat.pow_pos (by omega))
      have heq : 3 ^ e = 3 * 3 ^ (e - 1) := by
        cases e with | zero => omega | succ k => simp [Nat.pow_succ, Nat.mul_comm]
      omega⟩
  obtain ⟨i, j, hij, hgij⟩ := pigeonhole (Nat.lt_succ_self _) g
  let x := 1 + i.val * d
  let y := 1 + j.val * d
  have hxy : x < y := by
    have hd_pos : 0 < d := by
      cases d with | zero => simp at hmed; omega | succ _ => omega
    have : i.val * d < j.val * d := Nat.mul_lt_mul_of_pos_right hij hd_pos
    omega
  have hy_le : y ≤ 1 + m / 3 := by
    have hmul : 3 ^ (e - 1) * d = m / 3 := by
      have heq : 3 ^ e = 3 * 3 ^ (e - 1) := by
        cases e with | zero => omega | succ k => simp [Nat.pow_succ, Nat.mul_comm]
      rw [hmed, heq, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
    have hjle : j.val ≤ 3 ^ (e - 1) := by omega
    have := Nat.mul_le_mul_right d hjle
    omega
  have hmod3e : f x % 3 ^ e = f y % 3 ^ e := by
    have hdiv_eq : (f x % 3 ^ e) / 3 = (f y % 3 ^ e) / 3 := congrArg Fin.val hgij
    have h3e : 3 ∣ 3 ^ e := by
      cases e with | zero => omega | succ k => exact ⟨3 ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    have hmod_three : ∀ z, 3 ∣ f z → (f z % 3 ^ e) % 3 = 0 := by
      intro z ⟨b, hb⟩
      obtain ⟨a, ha⟩ := h3e
      have hdiv := Nat.div_add_mod (f z) (3 ^ e)
      have hdvd : 3 ∣ f z % 3 ^ e := by
        refine ⟨b - a * (f z / 3 ^ e), ?_⟩
        have h1 : 3 ^ e * (f z / 3 ^ e) = 3 * (a * (f z / 3 ^ e)) := by rw [ha, Nat.mul_assoc]
        rw [Nat.mul_sub, ← h1, ← hb]; omega
      exact Nat.mod_eq_zero_of_dvd hdvd
    have hx3 : (f x % 3 ^ e) % 3 = 0 := hmod_three x (three_dvd_f x)
    have hy3 : (f y % 3 ^ e) % 3 = 0 := hmod_three y (three_dvd_f y)
    have hx := Nat.div_add_mod (f x % 3 ^ e) 3
    have hy := Nat.div_add_mod (f y % 3 ^ e) 3
    omega
  have hdvd3e : 3 ^ e ∣ f y - f x := (mod_eq_iff_dvd_sub (f_mono (Nat.le_of_lt hxy))).mp hmod3e
  have hdvdd : d ∣ f y - f x := by
    rw [f_diff_eq (Nat.le_of_lt hxy)]
    have hyx : y - x = (j.val - i.val) * d := by
      dsimp only [x, y]; rw [Nat.add_sub_add_left, ← Nat.sub_mul]
    rw [hyx]
    exact ⟨(j.val - i.val) * (2 * (x ^ 2 + x * y + y ^ 2) + 1), by grind⟩
  have h3prime : IsPrime 3 := ⟨by omega, fun t ht => by
    have hle := Nat.le_of_dvd (by omega) ht
    have hne0 : t ≠ 0 := fun h0 => by rw [h0] at ht; exact absurd ht (by decide)
    have hne2 : t ≠ 2 := fun h2 => by rw [h2] at ht; exact absurd ht (by decide)
    omega⟩
  have hcop : Nat.gcd (3 ^ e) d = 1 := coprime_pow_left e (coprime_of_prime_not_dvd h3prime hnd3)
  have hdvdm : m ∣ f y - f x := by rw [hmed]; exact dvd_mul_of_coprime hcop hdvd3e hdvdd
  exact ⟨x, y, by omega, hxy, hy_le, (mod_eq_iff_dvd_sub (f_mono (Nat.le_of_lt hxy))).mpr hdvdm⟩

/-! ### Section 4: Pigeonhole Hensel Lifting (Lemma 2) -/

def ConicBox (p e : Nat) : Prop :=
  ∀ c : Nat, ¬ (p ∣ c) →
    ∃ u v : Nat,
      1 ≤ u ∧ u < v ∧ v ≤ (p ^ e - 1) / 2 ∧
      (u ^ 2 + u * v + v ^ 2) % p ^ e = c % p ^ e ∧
      ¬ (p ∣ (2 * u + v)) ∧ ¬ (p ∣ (u + 2 * v))

theorem pow_odd {p : Nat} (h : p % 2 = 1) (e : Nat) : p ^ e % 2 = 1 := by
  induction e with
  | zero => simp
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih, h]

theorem pigeonhole_hensel_lift {p e : Nat} (hp : IsPrime p) (hp5 : 5 ≤ p) (he : 1 ≤ e)
    (hbase : ConicBox p e) : ConicBox p (e + 1) := by
  intro c hndc
  obtain ⟨u1, v1, hu1, huv1, hv1, hmod1, ha_nd, hb_nd⟩ := hbase c hndc
  let a := 2 * u1 + v1
  let b := u1 + 2 * v1
  have hp_pos : 0 < p := by omega
  have hp_odd : p % 2 = 1 := by
    by_cases h2 : p % 2 = 0
    · have h2dvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h2
      rcases hp.2 2 h2dvd with h | h <;> omega
    · omega
  -- Find w ∈ [0, p-1] such that u1^2 + u1*v1 + v1^2 + p^e * w ≡ c (mod p^(e+1))
  have hpe_pos : 0 < p ^ e := Nat.pow_pos hp_pos
  have hdiff_dvd : (p ^ e : Int) ∣ ((c : Int) - ((u1 ^ 2 + u1 * v1 + v1 ^ 2 : Nat) : Int)) := by
    have h1 : ((u1 ^ 2 + u1 * v1 + v1 ^ 2 : Nat) : Int) % (p ^ e : Int) = (c : Int) % (p ^ e : Int) := by
      exact_mod_cast hmod1
    have h2 : ((c : Int) - ((u1 ^ 2 + u1 * v1 + v1 ^ 2 : Nat) : Int)) % (p ^ e : Int) = 0 := by
      rw [Int.sub_emod, h1, Int.sub_self, Int.zero_emod]
    exact Int.dvd_of_emod_eq_zero h2
  obtain ⟨qZ, hqZ⟩ := hdiff_dvd
  let w : Nat := (qZ % (p : Int)).toNat
  have hw_cast : (w : Int) = qZ % (p : Int) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  -- Solve a * k + b * l ≡ w (mod p) with 0 ≤ k, l ≤ (p - 1) / 2 via pigeonhole_two_maps!
  let half := (p + 1) / 2
  have hsum : p < half + half := by omega
  let g1 : Fin half → Fin p := fun k => ⟨(a * k.val) % p, Nat.mod_lt _ hp_pos⟩
  let g2 : Fin half → Fin p := fun l => ⟨(w + p - (b * l.val) % p) % p, Nat.mod_lt _ hp_pos⟩
  have hinj1 : ∀ i j : Fin half, g1 i = g1 j → i = j := by
    intro i j hEq
    have hval : (a * i.val) % p = (a * j.val) % p := congrArg Fin.val hEq
    apply Fin.ext
    suffices hle : ∀ r s, r < half → s < half → r ≤ s → (a * r) % p = (a * s) % p → r = s by
      rcases Nat.le_total i.val j.val with h | h
      · exact hle i.val j.val i.isLt j.isLt h hval
      · exact (hle j.val i.val j.isLt i.isLt h hval.symm).symm
    intro r s hr hs hrs hEq'
    have hdvd : p ∣ a * s - a * r := (mod_eq_iff_dvd_sub (Nat.mul_le_mul_left a hrs)).mp hEq'
    rw [← Nat.mul_sub] at hdvd
    rcases prime_dvd_mul hp hdvd with hpa | hps
    · exact absurd hpa ha_nd
    · have : s - r = 0 := Nat.eq_zero_of_dvd_of_lt hps (by omega)
      omega
  have hinj2 : ∀ i j : Fin half, g2 i = g2 j → i = j := by
    intro i j hEq
    have hval : (w + p - (b * i.val) % p) % p = (w + p - (b * j.val) % p) % p := congrArg Fin.val hEq
    have hmodb : (b * i.val) % p = (b * j.val) % p := by
      have hi_lt : (b * i.val) % p < p := Nat.mod_lt _ hp_pos
      have hj_lt : (b * j.val) % p < p := Nat.mod_lt _ hp_pos
      have hw_lt : w < p := by
        have := Int.emod_lt_of_pos qZ (show (0 : Int) < (p : Int) by omega)
        omega
      -- Both w + p - (b*i % p) and w + p - (b*j % p) lie in [w+1, w+p]
      -- If two numbers in [w+1, w+p] are congruent mod p, they are equal!
      have h1 : w + p - (b * i.val) % p = w + p - (b * j.val) % p := by
        have hle_or : w + p - (b * i.val) % p ≤ w + p - (b * j.val) % p ∨
                      w + p - (b * j.val) % p ≤ w + p - (b * i.val) % p := Nat.le_total _ _
        rcases hle_or with hle | hle
        · have hdvd := (mod_eq_iff_dvd_sub hle).mp hval
          have hzero := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
          omega
        · have hdvd := (mod_eq_iff_dvd_sub hle).mp hval.symm
          have hzero := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
          omega
      omega
    apply Fin.ext
    suffices hle : ∀ r s, r < half → s < half → r ≤ s → (b * r) % p = (b * s) % p → r = s by
      rcases Nat.le_total i.val j.val with h | h
      · exact hle i.val j.val i.isLt j.isLt h hmodb
      · exact (hle j.val i.val j.isLt i.isLt h hmodb.symm).symm
    intro r s hr hs hrs hEq'
    have hdvd : p ∣ b * s - b * r := (mod_eq_iff_dvd_sub (Nat.mul_le_mul_left b hrs)).mp hEq'
    rw [← Nat.mul_sub] at hdvd
    rcases prime_dvd_mul hp hdvd with hpb | hps
    · exact absurd hpb hb_nd
    · have : s - r = 0 := Nat.eq_zero_of_dvd_of_lt hps (by omega)
      omega
  obtain ⟨k, l, hkl⟩ := pigeonhole_two_maps hsum g1 g2 hinj1 hinj2
  have hkl_mod : ((a * k.val + b * l.val : Nat) : Int) % (p : Int) = (w : Int) % (p : Int) := by
    have hval : (a * k.val) % p = (w + p - (b * l.val) % p) % p := congrArg Fin.val hkl
    have hbl_lt : (b * l.val) % p < p := Nat.mod_lt _ hp_pos
    have hnat : (a * k.val + b * l.val) % p = w % p := by
      rw [Nat.add_mod, hval]
      have hsub_add : (w + p - b * l.val % p) % p + b * l.val % p =
                      (w + p - b * l.val % p) % p + (b * l.val % p) % p := by
        rw [Nat.mod_mod]
      rw [hsub_add, ← Nat.add_mod]
      have : w + p - b * l.val % p + b * l.val % p = w + p := by omega
      rw [this, Nat.add_mod_right]
    exact_mod_cast hnat
  -- Define u, v and verify all properties!
  let u := u1 + k.val * p ^ e
  let v := v1 + l.val * p ^ e
  have hpe_odd : p ^ e % 2 = 1 := pow_odd hp_odd e
  have hu_le : u ≤ (p ^ (e + 1) - 1) / 2 := by
    have hk_le : k.val ≤ (p - 1) / 2 := by omega
    have h1 : 2 * u1 ≤ p ^ e - 1 := by omega
    have h2 : 2 * k.val ≤ p - 1 := by omega
    have h3 : 2 * u ≤ p ^ (e + 1) - 1 := by
      rw [Nat.pow_succ]
      have : 2 * (u1 + k.val * p ^ e) = 2 * u1 + (2 * k.val) * p ^ e := by grind
      have hmul : (2 * k.val) * p ^ e ≤ (p - 1) * p ^ e := Nat.mul_le_mul_right (p ^ e) h2
      have hmul2 : (p - 1) * p ^ e + p ^ e = p ^ e * p := by
        cases p with | zero => omega | succ m => simp [Nat.succ_mul, Nat.mul_comm]
      omega
    omega
  have hv_le : v ≤ (p ^ (e + 1) - 1) / 2 := by
    have hl_le : l.val ≤ (p - 1) / 2 := by omega
    have h1 : 2 * v1 ≤ p ^ e - 1 := by omega
    have h2 : 2 * l.val ≤ p - 1 := by omega
    have h3 : 2 * v ≤ p ^ (e + 1) - 1 := by
      rw [Nat.pow_succ]
      have : 2 * (v1 + l.val * p ^ e) = 2 * v1 + (2 * l.val) * p ^ e := by grind
      have hmul : (2 * l.val) * p ^ e ≤ (p - 1) * p ^ e := Nat.mul_le_mul_right (p ^ e) h2
      have hmul2 : (p - 1) * p ^ e + p ^ e = p ^ e * p := by
        cases p with | zero => omega | succ m => simp [Nat.succ_mul, Nat.mul_comm]
      omega
    omega
  have huv_ne : u ≠ v := by
    intro hEq
    have hmod_pe : u % p ^ e = v % p ^ e := congrArg (· % p ^ e) hEq
    have hu1_lt : u1 < p ^ e := by omega
    have hv1_lt : v1 < p ^ e := by omega
    have h1 : u % p ^ e = u1 := by
      dsimp only [u]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu1_lt]
    have h2 : v % p ^ e = v1 := by
      dsimp only [v]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv1_lt]
    omega
  have hmod_next : (u ^ 2 + u * v + v ^ 2) % p ^ (e + 1) = c % p ^ (e + 1) := by
    -- Show p^(e+1) ∣ ((u^2 + u*v + v^2) - c) in Int
    have hdvd_p : (p : Int) ∣ (qZ - ((a * k.val + b * l.val : Nat) : Int)) := by
      have : (qZ - ((a * k.val + b * l.val : Nat) : Int)) % (p : Int) = 0 := by
        rw [Int.sub_emod, hkl_mod, hw_cast, Int.emod_emod, Int.sub_self, Int.zero_emod]
      exact Int.dvd_of_emod_eq_zero this
    obtain ⟨tZ, htZ⟩ := hdvd_p
    have hpe_dvd_pe2 : (p ^ (e + 1) : Int) ∣ (p ^ e : Int) * (p ^ e : Int) := by
      have : p ^ (e + 1) ∣ p ^ e * p ^ e := by
        rw [Nat.pow_succ]
        have hpe1 : p ∣ p ^ e := by
          cases e with | zero => omega | succ m => exact ⟨p ^ m, by rw [Nat.pow_succ, Nat.mul_comm]⟩
        obtain ⟨r, hr⟩ := hpe1
        exact ⟨r, by rw [hr]; grind⟩
      exact_mod_cast this
    obtain ⟨sZ, hsZ⟩ := hpe_dvd_pe2
    have hdiffZ : ((u ^ 2 + u * v + v ^ 2 : Nat) : Int) - (c : Int) =
                  (p ^ (e + 1) : Int) * (-tZ + sZ * ((k.val : Int) ^ 2 + (k.val : Int) * (l.val : Int) + (l.val : Int) ^ 2)) := by
      have hpow : (p ^ (e + 1) : Int) = (p ^ e : Int) * (p : Int) := by rw [Int.pow_succ]
      dsimp only [u, v, a, b]
      push_cast
      grind
    have hmodZ : ((u ^ 2 + u * v + v ^ 2 : Nat) : Int) % (p ^ (e + 1) : Int) = (c : Int) % (p ^ (e + 1) : Int) := by
      have : ((u ^ 2 + u * v + v ^ 2 : Nat) : Int) = (c : Int) + (p ^ (e + 1) : Int) * (-tZ + sZ * ((k.val : Int) ^ 2 + (k.val : Int) * (l.val : Int) + (l.val : Int) ^ 2)) := by
        omega
      rw [this, Int.add_mul_emod_self_left]
    exact_mod_cast hmodZ
  have h2uv_nd : ¬ p ∣ (2 * u + v) := by
    intro hdvd
    apply ha_nd
    have hpe : p ∣ p ^ e := by
      cases e with | zero => omega | succ m => exact ⟨p ^ m, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    obtain ⟨r, hr⟩ := hpe
    obtain ⟨s, hs⟩ := hdvd
    have : 2 * u + v = a + p * (r * (2 * k.val + l.val)) := by
      dsimp only [u, v, a]; rw [hr]; grind
    exact ⟨s - r * (2 * k.val + l.val), by
      have : p * s = a + p * (r * (2 * k.val + l.val)) := by omega
      rw [Nat.mul_sub]; omega⟩
  have hu2v_nd : ¬ p ∣ (u + 2 * v) := by
    intro hdvd
    apply hb_nd
    have hpe : p ∣ p ^ e := by
      cases e with | zero => omega | succ m => exact ⟨p ^ m, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    obtain ⟨r, hr⟩ := hpe
    obtain ⟨s, hs⟩ := hdvd
    have : u + 2 * v = b + p * (r * (k.val + 2 * l.val)) := by
      dsimp only [u, v, b]; rw [hr]; grind
    exact ⟨s - r * (k.val + 2 * l.val), by
      have : p * s = b + p * (r * (k.val + 2 * l.val)) := by omega
      rw [Nat.mul_sub]; omega⟩
  rcases Nat.lt_or_gt_of_ne huv_ne with hlt | hgt
  · exact ⟨u, v, by omega, hlt, hv_le, hmod_next, h2uv_nd, hu2v_nd⟩
  · refine ⟨v, u, by omega, hgt, hu_le, ?_, ?_, ?_⟩
    · have : v ^ 2 + v * u + u ^ 2 = u ^ 2 + u * v + v ^ 2 := by grind
      rw [this]; exact hmod_next
    · rw [Nat.add_comm]; exact hu2v_nd
    · rw [Nat.add_comm]; exact h2uv_nd

theorem conicBox_of_base {p e0 : Nat} (hp : IsPrime p) (hp5 : 5 ≤ p) (he0 : 1 ≤ e0)
    (hbase : ConicBox p e0) : ∀ e, e0 ≤ e → ConicBox p e := by
  intro e he
  induction e with
  | zero => omega
  | succ k ih =>
    by_cases hEq : k + 1 = e0
    · rw [hEq]; exact hbase
    · exact pigeonhole_hensel_lift hp hp5 (by omega) (ih (by omega))

/-! ### Section 5: Purely Algebraic Conic Box Lemma for All Primes p ≥ 17 -/

/-- Any list of fewer than p elements of Fin p omits some element of Fin p. -/
theorem exists_not_in_list {p : Nat} (L : List (Fin p)) (hL : L.length < p) :
    ∃ t : Fin p, t ∉ L := by
  -- Proof by contradiction using pigeonhole: if every t ∈ L, pick its index in L.
  apply Classical.byContradiction
  intro hall
  have hmem : ∀ t : Fin p, ∃ i : Fin L.length, L[i.val] = t := by
    intro t
    have htL : t ∈ L := Classical.byContradiction fun hnt => hall ⟨t, hnt⟩
    have hidx : ∀ (xs : List (Fin p)), t ∈ xs → ∃ i : Fin xs.length, xs[i.val] = t := by
      intro xs
      induction xs with
      | nil => intro h; cases h
      | cons a as ih =>
        intro h
        cases h with
        | head => exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩
        | tail _ hmem' =>
          obtain ⟨i, hi⟩ := ih hmem'
          exact ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, hi⟩
    exact hidx L htL
  let g : Fin p → Fin L.length := fun t => Classical.choose (hmem t)
  obtain ⟨t1, t2, hlt, hg⟩ := pigeonhole hL g
  have h1 : L[(g t1).val] = t1 := Classical.choose_spec (hmem t1)
  have h2 : L[(g t2).val] = t2 := Classical.choose_spec (hmem t2)
  have htEq : t1 = t2 := by
    have hL_eq : L[(g t1).val] = L[(g t2).val] := by simp [hg]
    rw [h1, h2] at hL_eq
    exact hL_eq
  subst htEq; omega

/-- Modulo a prime p, x^2 ≡ y^2 (mod p) implies x ≡ y or x + y ≡ 0 (mod p). -/
theorem prime_sq_eq_mod {p x y : Nat} (hp : IsPrime p) (hx : x < p) (hy : y < p)
    (h : x ^ 2 % p = y ^ 2 % p) : x = y ∨ x + y = p := by
  have hdvd : (p : Int) ∣ ((x : Int) - (y : Int)) * ((x : Int) + (y : Int)) := by
    have h1 : ((x : Int) ^ 2 - (y : Int) ^ 2) % (p : Int) = 0 := by
      rw [Int.sub_emod]
      have hx2 : ((x : Int) ^ 2) % (p : Int) = ((x ^ 2 % p : Nat) : Int) := by norm_cast
      have hy2 : ((y : Int) ^ 2) % (p : Int) = ((y ^ 2 % p : Nat) : Int) := by norm_cast
      rw [hx2, hy2, h, Int.sub_self, Int.zero_emod]
    have h2 : ((x : Int) - (y : Int)) * ((x : Int) + (y : Int)) = (x : Int) ^ 2 - (y : Int) ^ 2 := by grind
    rw [h2]; exact Int.dvd_of_emod_eq_zero h1
  by_cases hxy0 : x + y = 0
  · left; omega
  have hsum_eq : p ∣ x + y → x + y = p := by
    intro ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ r =>
        have : p * (r + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
        omega
  rcases Nat.le_total y x with hyx | hxy
  · have hnat : p ∣ (x - y) * (x + y) := by
      have : (((x - y) * (x + y) : Nat) : Int) = ((x : Int) - (y : Int)) * ((x : Int) + (y : Int)) := by
        push_cast; rw [Int.ofNat_sub hyx]
      rw [← this] at hdvd; exact Int.ofNat_dvd.mp hdvd
    rcases prime_dvd_mul hp hnat with h1 | h2
    · left; have := Nat.eq_zero_of_dvd_of_lt h1 (by omega); omega
    · exact Or.inr (hsum_eq h2)
  · have hnat : p ∣ (y - x) * (x + y) := by
      have : (((y - x) * (x + y) : Nat) : Int) = -(((x : Int) - (y : Int)) * ((x : Int) + (y : Int))) := by
        push_cast; rw [Int.ofNat_sub hxy]; grind
      have hdvd' : (p : Int) ∣ -(((x : Int) - (y : Int)) * ((x : Int) + (y : Int))) := Int.dvd_neg.mpr hdvd
      rw [← this] at hdvd'; exact Int.ofNat_dvd.mp hdvd'
    rcases prime_dvd_mul hp hnat with h1 | h2
    · left; have := Nat.eq_zero_of_dvd_of_lt h1 (by omega); omega
    · exact Or.inr (hsum_eq h2)

/-- At most 2 elements of Fin p satisfy a predicate whose image under an injective map has fixed square mod p. -/
theorem at_most_two_of_sq {p : Nat} (hp : IsPrime p) (P : Fin p → Prop) (val : Fin p → Nat)
    (hval_lt : ∀ t, P t → val t < p)
    (hinj : ∀ t1 t2, P t1 → P t2 → val t1 = val t2 → t1 = t2)
    (a : Nat) (hsq : ∀ t, P t → (val t) ^ 2 % p = a % p) :
    ∃ L : List (Fin p), L.length ≤ 2 ∧ ∀ t, P t → t ∈ L := by
  by_cases h1 : ∃ t1, P t1
  · obtain ⟨t1, ht1⟩ := h1
    by_cases h2 : ∃ t2, P t2 ∧ t2 ≠ t1
    · obtain ⟨t2, ht2, hne⟩ := h2
      refine ⟨[t1, t2], by simp, fun t ht => ?_⟩
      have hsq1 : (val t) ^ 2 % p = (val t1) ^ 2 % p := by rw [hsq t ht, hsq t1 ht1]
      have hsq2 : (val t2) ^ 2 % p = (val t1) ^ 2 % p := by rw [hsq t2 ht2, hsq t1 ht1]
      have hne_val : val t2 ≠ val t1 := fun hEq => hne (hinj t2 t1 ht2 ht1 hEq)
      have h21 : val t2 + val t1 = p := by
        rcases prime_sq_eq_mod hp (hval_lt t2 ht2) (hval_lt t1 ht1) hsq2 with h | h
        · exact absurd h hne_val
        · exact h
      rcases prime_sq_eq_mod hp (hval_lt t ht) (hval_lt t1 ht1) hsq1 with h | h
      · have : t = t1 := hinj t t1 ht ht1 h
        rw [this]; simp
      · have : val t = val t2 := by omega
        have : t = t2 := hinj t t2 ht ht2 this
        rw [this]; simp
    · refine ⟨[t1], by simp, fun t ht => ?_⟩
      have : t = t1 := Classical.byContradiction fun hne => h2 ⟨t, ht, hne⟩
      rw [this]; simp
  · exact ⟨[], by simp, fun t ht => absurd ⟨t, ht⟩ h1⟩

/-- At most 4 elements of Fin p satisfy a predicate whose image under an injective pair map has fixed squares mod p. -/
theorem at_most_four_of_pair_sq {p : Nat} (hp : IsPrime p) (P : Fin p → Prop)
    (X Y : Fin p → Nat)
    (hX_lt : ∀ t, P t → X t < p) (hY_lt : ∀ t, P t → Y t < p)
    (hinj : ∀ t1 t2, P t1 → P t2 → X t1 = X t2 → Y t1 = Y t2 → t1 = t2)
    (a b : Nat) (hXsq : ∀ t, P t → (X t) ^ 2 % p = a % p)
    (hYsq : ∀ t, P t → (Y t) ^ 2 % p = b % p) :
    ∃ L : List (Fin p), L.length ≤ 4 ∧ ∀ t, P t → t ∈ L := by
  by_cases h0 : ∃ t0, P t0
  · obtain ⟨t0, ht0⟩ := h0
    -- Split P into two sub-predicates: X t = X t0, and X t ≠ X t0 (hence X t = p - X t0)
    let P1 : Fin p → Prop := fun t => P t ∧ X t = X t0
    let P2 : Fin p → Prop := fun t => P t ∧ X t ≠ X t0
    obtain ⟨L1, hL1, hmem1⟩ := at_most_two_of_sq hp P1 Y
      (fun t ht => hY_lt t ht.1)
      (fun t1 t2 h1 h2 hY => hinj t1 t2 h1.1 h2.1 (by rw [h1.2, h2.2]) hY)
      b (fun t ht => hYsq t ht.1)
    obtain ⟨L2, hL2, hmem2⟩ := at_most_two_of_sq hp P2 Y
      (fun t ht => hY_lt t ht.1)
      (fun t1 t2 h1 h2 hY => by
        have hx1 : X t1 + X t0 = p := by
          rcases prime_sq_eq_mod hp (hX_lt t1 h1.1) (hX_lt t0 ht0) (by rw [hXsq t1 h1.1, hXsq t0 ht0]) with h | h
          · exact absurd h h1.2
          · exact h
        have hx2 : X t2 + X t0 = p := by
          rcases prime_sq_eq_mod hp (hX_lt t2 h2.1) (hX_lt t0 ht0) (by rw [hXsq t2 h2.1, hXsq t0 ht0]) with h | h
          · exact absurd h h2.2
          · exact h
        exact hinj t1 t2 h1.1 h2.1 (by omega) hY)
      b (fun t ht => hYsq t ht.1)
    refine ⟨L1 ++ L2, by simp; omega, fun t ht => ?_⟩
    by_cases hX : X t = X t0
    · exact List.mem_append_left L2 (hmem1 t ⟨ht, hX⟩)
    · exact List.mem_append_right L1 (hmem2 t ⟨ht, hX⟩)
  · exact ⟨[], by simp, fun t ht => absurd ⟨t, ht⟩ h0⟩

/-- There exists at least one point (X0, Y0) on X^2 + 3*Y^2 ≡ 4*c (mod p) for any odd prime p. -/
theorem exists_conic_point {p : Nat} (hp : IsPrime p) (hp5 : 5 ≤ p) (c : Nat) :
    ∃ X0 Y0 : Nat, X0 < p ∧ Y0 < p ∧ (X0 ^ 2 + 3 * Y0 ^ 2) % p = (4 * c) % p := by
  have hp_pos : 0 < p := by omega
  have hp_odd : p % 2 = 1 := by
    by_cases h2 : p % 2 = 0
    · rcases hp.2 2 (Nat.dvd_of_mod_eq_zero h2) with h | h <;> omega
    · omega
  let half := (p + 1) / 2
  have hsum : p < half + half := by omega
  let g1 : Fin half → Fin p := fun x => ⟨(x.val ^ 2) % p, Nat.mod_lt _ hp_pos⟩
  let g2 : Fin half → Fin p := fun y => ⟨((4 * c) % p + p - (3 * y.val ^ 2) % p) % p, Nat.mod_lt _ hp_pos⟩
  have hinj1 : ∀ i j : Fin half, g1 i = g1 j → i = j := by
    intro i j hEq
    have hval : i.val ^ 2 % p = j.val ^ 2 % p := congrArg Fin.val hEq
    rcases prime_sq_eq_mod hp (by omega) (by omega) hval with h | h
    · exact Fin.ext h
    · omega
  have hinj2 : ∀ i j : Fin half, g2 i = g2 j → i = j := by
    intro i j hEq
    have hval : ((4 * c) % p + p - (3 * i.val ^ 2) % p) % p =
                ((4 * c) % p + p - (3 * j.val ^ 2) % p) % p := congrArg Fin.val hEq
    have hi_lt : (3 * i.val ^ 2) % p < p := Nat.mod_lt _ hp_pos
    have hj_lt : (3 * j.val ^ 2) % p < p := Nat.mod_lt _ hp_pos
    have h3eq : (3 * i.val ^ 2) % p = (3 * j.val ^ 2) % p := by
      have h1 : (4 * c) % p + p - (3 * i.val ^ 2) % p = (4 * c) % p + p - (3 * j.val ^ 2) % p := by
        rcases Nat.le_total ((4 * c) % p + p - (3 * i.val ^ 2) % p) ((4 * c) % p + p - (3 * j.val ^ 2) % p) with hle | hle
        · have hdvd := (mod_eq_iff_dvd_sub hle).mp hval
          have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); omega
        · have hdvd := (mod_eq_iff_dvd_sub hle).mp hval.symm
          have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); omega
      omega
    have hsq : i.val ^ 2 % p = j.val ^ 2 % p := by
      suffices hle : ∀ r s, r < half → s < half → r ≤ s → (3 * r ^ 2) % p = (3 * s ^ 2) % p → r ^ 2 % p = s ^ 2 % p by
        rcases Nat.le_total i.val j.val with h | h
        · exact hle i.val j.val i.isLt j.isLt h h3eq
        · exact (hle j.val i.val j.isLt i.isLt h h3eq.symm).symm
      intro r s hr hs hrs hEq'
      have hle2 : r ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hrs 2
      have hdvd : p ∣ 3 * s ^ 2 - 3 * r ^ 2 := (mod_eq_iff_dvd_sub (Nat.mul_le_mul_left 3 hle2)).mp hEq'
      rw [← Nat.mul_sub] at hdvd
      have hnd3 : ¬ p ∣ 3 := fun h3 => by have := Nat.le_of_dvd (by omega) h3; omega
      rcases prime_dvd_mul hp hdvd with h3 | hsr
      · exact absurd h3 hnd3
      · exact (mod_eq_iff_dvd_sub hle2).mpr hsr
    rcases prime_sq_eq_mod hp (by omega) (by omega) hsq with h | h
    · exact Fin.ext h
    · omega
  obtain ⟨x, y, hxy⟩ := pigeonhole_two_maps hsum g1 g2 hinj1 hinj2
  have hval : x.val ^ 2 % p = ((4 * c) % p + p - (3 * y.val ^ 2) % p) % p := congrArg Fin.val hxy
  have hylt : (3 * y.val ^ 2) % p < p := Nat.mod_lt _ hp_pos
  refine ⟨x.val, y.val, by omega, by omega, ?_⟩
  rw [Nat.add_mod, hval]
  have h1 : ((4 * c) % p + p - 3 * y.val ^ 2 % p) % p + 3 * y.val ^ 2 % p =
            ((4 * c) % p + p - 3 * y.val ^ 2 % p) % p + (3 * y.val ^ 2 % p) % p := by rw [Nat.mod_mod]
  rw [h1, ← Nat.add_mod]
  have h2 : (4 * c) % p + p - 3 * y.val ^ 2 % p + 3 * y.val ^ 2 % p = (4 * c) % p + p := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_mod]

/-- Standalone polynomial identities for stereographic projection (keeps `grind` instant). -/
theorem int_cancel_coprime (P A B RX RY Q : Int)
    (h1 : (1 : Int) = P * RX + A * RY) (h2 : A * B = P * Q) :
    B = P * (B * RX + Q * RY) := by
  grind

theorem stereo_pt_id (X0 Y0 t X Y c p kx ky k0 : Int)
    (hx : (t ^ 2 + 3) * X - (X0 * (t ^ 2 - 3) - 6 * Y0 * t) = p * kx)
    (hy : (t ^ 2 + 3) * Y - (Y0 * (3 - t ^ 2) - 2 * X0 * t) = p * ky)
    (h0 : X0 ^ 2 + 3 * Y0 ^ 2 - 4 * c = p * k0) :
    (t ^ 2 + 3) ^ 2 * (X ^ 2 + 3 * Y ^ 2 - 4 * c) =
      p * (((t ^ 2 + 3) * X + (X0 * (t ^ 2 - 3) - 6 * Y0 * t)) * kx +
           3 * ((t ^ 2 + 3) * Y + (Y0 * (3 - t ^ 2) - 2 * X0 * t)) * ky +
           (t ^ 2 + 3) ^ 2 * k0) := by
  have hpoly : (X0 * (t ^ 2 - 3) - 6 * Y0 * t) ^ 2 + 3 * (Y0 * (3 - t ^ 2) - 2 * X0 * t) ^ 2 =
               (t ^ 2 + 3) ^ 2 * (X0 ^ 2 + 3 * Y0 ^ 2) := by grind
  grind

theorem stereo_A_id (X0 Y0 t X Y c p kx ky k0 : Int)
    (hx : (t ^ 2 + 3) * X - (X0 * (t ^ 2 - 3) - 6 * Y0 * t) = p * kx)
    (hy : (t ^ 2 + 3) * Y - (Y0 * (3 - t ^ 2) - 2 * X0 * t) = p * ky)
    (h0 : X0 ^ 2 + 3 * Y0 ^ 2 - 4 * c = p * k0) :
    (t ^ 2 + 3) * (X0 * (X - X0) - 3 * Y0 * (Y + Y0)) + 24 * c =
      p * (X0 * kx - 3 * Y0 * ky - 6 * k0) := by
  grind

theorem stereo_B_id (X0 Y0 t X Y c p kx ky k0 : Int)
    (hx : (t ^ 2 + 3) * X - (X0 * (t ^ 2 - 3) - 6 * Y0 * t) = p * kx)
    (hy : (t ^ 2 + 3) * Y - (Y0 * (3 - t ^ 2) - 2 * X0 * t) = p * ky)
    (h0 : X0 ^ 2 + 3 * Y0 ^ 2 - 4 * c = p * k0) :
    (t ^ 2 + 3) * (Y0 * (X - X0) + X0 * (Y + Y0)) + 8 * c * t =
      p * (Y0 * kx + X0 * ky - 2 * t * k0) := by
  grind

theorem stereo_elim_id (d1 d2 A B c t1 t2 p qa1 qb1 qa2 qb2 : Int)
    (hA1 : d1 * A + 24 * c = p * qa1)
    (hB1 : d1 * B + 8 * c * t1 = p * qb1)
    (hA2 : d2 * A + 24 * c = p * qa2)
    (hB2 : d2 * B + 8 * c * t2 = p * qb2) :
    d2 * (24 * c) * (t1 - t2) =
      p * (d2 * qa1 * (t1 - t2) - (d1 * (3 * qb2 - t2 * qa2) - d2 * (3 * qb1 - t1 * qa1))) := by
  have h1 : d1 * (3 * B - t1 * A) = p * (3 * qb1 - t1 * qa1) := by grind
  have h2 : d2 * (3 * B - t2 * A) = p * (3 * qb2 - t2 * qa2) := by grind
  have h3 : d1 * d2 * A * (t1 - t2) = p * (d1 * (3 * qb2 - t2 * qa2) - d2 * (3 * qb1 - t1 * qa1)) := by grind
  grind

/-- Standalone 2-case parity construction from (X, Y) in [1, (p-1)/2]^2 to (u, v) in [1, (p-1)/2]^2. -/
theorem conicBox_from_XY {p c X Y inv4 : Nat} (hp_odd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hinv4 : (4 * inv4) % p = 1)
    (hX_range : 1 ≤ X ∧ X ≤ (p - 1) / 2)
    (hY_range : 1 ≤ Y ∧ Y ≤ (p - 1) / 2)
    (hXY_ne : X ≠ Y)
    (hXY_conic : (X ^ 2 + 3 * Y ^ 2) % p = (4 * c) % p)
    (h3Y2_ne : (3 * Y ^ 2) % p ≠ c % p) :
    ∃ u v : Nat,
      1 ≤ u ∧ u < v ∧ v ≤ (p - 1) / 2 ∧
      (u ^ 2 + u * v + v ^ 2) % p = c % p ∧
      ¬ (p ∣ (2 * u + v)) ∧ ¬ (p ∣ (u + 2 * v)) := by
  have hcancel4 : ∀ A : Nat, (4 * A) % p = (4 * c) % p → A % p = c % p := by
    intro A h4
    have h1 : A % p = ((4 * A) * inv4) % p := by
      have : (4 * A) * inv4 = (4 * inv4) * A := by grind
      rw [this, Nat.mul_mod, hinv4, Nat.one_mul, Nat.mod_mod]
    have h2 : c % p = ((4 * c) * inv4) % p := by
      have : (4 * c) * inv4 = (4 * inv4) * c := by grind
      rw [this, Nat.mul_mod, hinv4, Nat.one_mul, Nat.mod_mod]
    rw [h1, Nat.mul_mod, h4, ← Nat.mul_mod, ← h2]
  by_cases hpar : X % 2 = Y % 2
  · rcases Nat.lt_or_gt_of_ne hXY_ne with hlt | hgt
    · let u := (Y - X) / 2
      let v := (X + Y) / 2
      refine ⟨u, v, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · apply hcancel4
        have h4eq : 4 * (u ^ 2 + u * v + v ^ 2) = X ^ 2 + 3 * Y ^ 2 := by
          have hZ : (4 * (u ^ 2 + u * v + v ^ 2) : Int) = (X : Int) ^ 2 + 3 * (Y : Int) ^ 2 := by
            have huZ : 2 * (u : Int) = (Y : Int) - (X : Int) := by omega
            have hvZ : 2 * (v : Int) = (X : Int) + (Y : Int) := by omega
            grind
          exact_mod_cast hZ
        rw [h4eq]; exact hXY_conic
      · intro hdvd
        have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); omega
      · intro hdvd
        have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); omega
    · let u := (X - Y) / 2
      let v := Y
      have h4eq : 4 * (u ^ 2 + u * v + v ^ 2) = X ^ 2 + 3 * Y ^ 2 := by
        have hZ : (4 * (u ^ 2 + u * v + v ^ 2) : Int) = (X : Int) ^ 2 + 3 * (Y : Int) ^ 2 := by
          have huZ : 2 * (u : Int) = (X : Int) - (Y : Int) := by omega
          have hvZ : (v : Int) = (Y : Int) := rfl
          grind
        exact_mod_cast hZ
      have hmod_uv : (u ^ 2 + u * v + v ^ 2) % p = c % p := hcancel4 _ (by rw [h4eq]; exact hXY_conic)
      have huv_ne : u ≠ v := by
        intro hEq
        have hX3Y : X = 3 * Y := by omega
        have h12 : (4 * (3 * Y ^ 2)) % p = (4 * c) % p := by
          have : X ^ 2 + 3 * Y ^ 2 = 4 * (3 * Y ^ 2) := by rw [hX3Y]; grind
          rw [← this]; exact hXY_conic
        exact h3Y2_ne (hcancel4 _ h12)
      have h2uv_nd : ¬ p ∣ (2 * u + v) := fun hdvd => by
        have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); omega
      have hu2v_nd : ¬ p ∣ (u + 2 * v) := fun hdvd => by
        have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); omega
      rcases Nat.lt_or_gt_of_ne huv_ne with h1 | h2
      · exact ⟨u, v, by omega, h1, by omega, hmod_uv, h2uv_nd, hu2v_nd⟩
      · refine ⟨v, u, by omega, h2, by omega, ?_, ?_, ?_⟩
        · have : v ^ 2 + v * u + u ^ 2 = u ^ 2 + u * v + v ^ 2 := by grind
          rw [this]; exact hmod_uv
        · rw [Nat.add_comm]; exact hu2v_nd
        · rw [Nat.add_comm]; exact h2uv_nd
  · let u := (p - X - Y) / 2
    let v := Y
    have h4eq_mod : (4 * (u ^ 2 + u * v + v ^ 2)) % p = (4 * c) % p := by
      have h4eq : 4 * (u ^ 2 + u * v + v ^ 2) = (p - X) ^ 2 + 3 * Y ^ 2 := by
        have hZ : (4 * (u ^ 2 + u * v + v ^ 2) : Int) = ((p - X : Nat) : Int) ^ 2 + 3 * (Y : Int) ^ 2 := by
          have huZ : 2 * (u : Int) = ((p - X : Nat) : Int) - (Y : Int) := by omega
          have hvZ : (v : Int) = (Y : Int) := rfl
          grind
        exact_mod_cast hZ
      rw [h4eq]
      have hZ : ((((p - X : Nat) : Int) ^ 2 + 3 * (Y : Int) ^ 2) - ((X : Int) ^ 2 + 3 * (Y : Int) ^ 2)) % (p : Int) = 0 := by
        have hsub : ((p - X : Nat) : Int) = (p : Int) - (X : Int) := Int.ofNat_sub (by omega)
        rw [hsub]
        have : ((p : Int) - (X : Int)) ^ 2 + 3 * (Y : Int) ^ 2 - ((X : Int) ^ 2 + 3 * (Y : Int) ^ 2) =
               (p : Int) * ((p : Int) - 2 * (X : Int)) := by grind
        rw [this, Int.mul_emod_right]
      have hmodZ : (((p - X) ^ 2 + 3 * Y ^ 2 : Nat) : Int) % (p : Int) = ((X ^ 2 + 3 * Y ^ 2 : Nat) : Int) % (p : Int) := by
        obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hZ
        have : (((p - X) ^ 2 + 3 * Y ^ 2 : Nat) : Int) = ((X ^ 2 + 3 * Y ^ 2 : Nat) : Int) + (p : Int) * q := by
          push_cast; omega
        rw [this, Int.add_mul_emod_self_left]
      have hnat : ((p - X) ^ 2 + 3 * Y ^ 2) % p = (X ^ 2 + 3 * Y ^ 2) % p := by exact_mod_cast hmodZ
      rw [hnat]; exact hXY_conic
    have hmod_uv : (u ^ 2 + u * v + v ^ 2) % p = c % p := hcancel4 _ h4eq_mod
    have h12_of_eq : (X + 3 * Y = p ∨ 3 * Y = p + X) → (4 * (3 * Y ^ 2)) % p = (4 * c) % p := by
      intro hcase
      have hZ : ((X : Int) ^ 2 + 3 * (Y : Int) ^ 2 - 12 * (Y : Int) ^ 2) % (p : Int) = 0 := by
        rcases hcase with h1 | h2
        · have : (X : Int) = (p : Int) - 3 * (Y : Int) := by omega
          rw [this]
          have : ((p : Int) - 3 * (Y : Int)) ^ 2 + 3 * (Y : Int) ^ 2 - 12 * (Y : Int) ^ 2 =
                 (p : Int) * ((p : Int) - 6 * (Y : Int)) := by grind
          rw [this, Int.mul_emod_right]
        · have : (X : Int) = 3 * (Y : Int) - (p : Int) := by omega
          rw [this]
          have : (3 * (Y : Int) - (p : Int)) ^ 2 + 3 * (Y : Int) ^ 2 - 12 * (Y : Int) ^ 2 =
                 (p : Int) * ((p : Int) - 6 * (Y : Int)) := by grind
          rw [this, Int.mul_emod_right]
      have hmodZ : ((X ^ 2 + 3 * Y ^ 2 : Nat) : Int) % (p : Int) = ((4 * (3 * Y ^ 2) : Nat) : Int) % (p : Int) := by
        obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hZ
        have : ((X ^ 2 + 3 * Y ^ 2 : Nat) : Int) = ((4 * (3 * Y ^ 2) : Nat) : Int) + (p : Int) * q := by
          push_cast; omega
        rw [this, Int.add_mul_emod_self_left]
      have hnat : (X ^ 2 + 3 * Y ^ 2) % p = (4 * (3 * Y ^ 2)) % p := by exact_mod_cast hmodZ
      rw [← hnat]; exact hXY_conic
    have huv_ne : u ≠ v := fun hEq => h3Y2_ne (hcancel4 _ (h12_of_eq (Or.inl (by omega))))
    have h2uv_nd : ¬ p ∣ (2 * u + v) := fun hdvd => by
      have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); omega
    have hu2v_nd : ¬ p ∣ (u + 2 * v) := fun hdvd => by
      obtain ⟨k, hk⟩ := hdvd
      have hk1 : k = 1 := by
        cases k with
        | zero => omega
        | succ m =>
          cases m with
          | zero => rfl
          | succ r =>
            have : p * (r + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
            omega
      rw [hk1, Nat.mul_one] at hk
      have hu2 : 2 * u = p - X - Y := by omega
      exact h3Y2_ne (hcancel4 _ (h12_of_eq (Or.inr (by omega))))
    rcases Nat.lt_or_gt_of_ne huv_ne with h1 | h2
    · exact ⟨u, v, by omega, h1, by omega, hmod_uv, h2uv_nd, hu2v_nd⟩
    · refine ⟨v, u, by omega, h2, by omega, ?_, ?_, ?_⟩
      · have : v ^ 2 + v * u + u ^ 2 = u ^ 2 + u * v + v ^ 2 := by grind
        rw [this]; exact hmod_uv
      · rw [Nat.add_comm]; exact hu2v_nd
      · rw [Nat.add_comm]; exact h2uv_nd

/-- Lemma 3 (Conic Box Lemma): Purely algebraic proof for ALL primes p ≥ 17! -/
theorem conicBox_prime {p : Nat} (hp : IsPrime p) (hp17 : 17 ≤ p) : ConicBox p 1 := by
  intro c hndc
  rw [Nat.pow_one]
  have hp_pos : 0 < p := by omega
  have hp_odd : p % 2 = 1 := by
    by_cases h2 : p % 2 = 0
    · rcases hp.2 2 (Nat.dvd_of_mod_eq_zero h2) with h | h <;> omega
    · omega
  have hnd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hnd3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  obtain ⟨X0, Y0, hX0_lt, hY0_lt, hpt0⟩ := exists_conic_point hp (by omega) c
  -- For each t : Fin p with ¬ p ∣ (t^2 + 3), choose inv(t) with ((t^2 + 3) * inv(t)) % p = 1.
  let denom (t : Fin p) : Nat := t.val ^ 2 + 3
  let invD (t : Fin p) : Nat :=
    if h : ¬ p ∣ denom t then
      Classical.choose (exists_mod_inv hp_pos (by rw [Nat.gcd_comm]; exact coprime_of_prime_not_dvd hp h))
    else 0
  have hinvD : ∀ t : Fin p, ¬ p ∣ denom t → (denom t * invD t) % p = 1 := by
    intro t h
    dsimp only [invD]
    rw [dite_eq_left h]
    have hspec := (Classical.choose_spec (exists_mod_inv hp_pos (by rw [Nat.gcd_comm]; exact coprime_of_prime_not_dvd hp h))).2
    exact hspec.trans (Nat.mod_eq_of_lt (by omega : 1 < p))
  -- Stereographic projection (in Int, reduced mod p to Nat in [0, p-1]):
  let Xnum (t : Fin p) : Int := (X0 : Int) * ((t.val : Int) ^ 2 - 3) - 6 * (Y0 : Int) * (t.val : Int)
  let Ynum (t : Fin p) : Int := (Y0 : Int) * (3 - (t.val : Int) ^ 2) - 2 * (X0 : Int) * (t.val : Int)
  let Xf (t : Fin p) : Nat := ((Xnum t * (invD t : Int)) % (p : Int)).toNat
  let Yf (t : Fin p) : Nat := ((Ynum t * (invD t : Int)) % (p : Int)).toNat
  have hXf_lt : ∀ t, Xf t < p := fun t => by
    have h1 := Int.emod_nonneg (Xnum t * (invD t : Int)) (show (p : Int) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos (Xnum t * (invD t : Int)) (show (0 : Int) < (p : Int) by omega)
    dsimp only [Xf]; omega
  have hYf_lt : ∀ t, Yf t < p := fun t => by
    have h1 := Int.emod_nonneg (Ynum t * (invD t : Int)) (show (p : Int) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos (Ynum t * (invD t : Int)) (show (0 : Int) < (p : Int) by omega)
    dsimp only [Yf]; omega
  have hXf_cast : ∀ t, (Xf t : Int) = (Xnum t * (invD t : Int)) % (p : Int) := fun t =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hYf_cast : ∀ t, (Yf t : Int) = (Ynum t * (invD t : Int)) % (p : Int) := fun t =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  -- Key congruence: (denom t) * Xf t ≡ Xnum t (mod p), and same for Yf t
  have hDX : ∀ t, ¬ p ∣ denom t → (p : Int) ∣ ((denom t : Int) * (Xf t : Int) - Xnum t) := by
    intro t ht
    have hinv : (p : Int) ∣ ((denom t : Int) * (invD t : Int) - 1) := by
      have h1 : ((denom t * invD t : Nat) : Int) % (p : Int) = 1 := by exact_mod_cast hinvD t ht
      have h2 : ((denom t : Int) * (invD t : Int) - 1) % (p : Int) = 0 := by
        rw [Int.sub_emod]; push_cast at h1; rw [h1, Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 1) (by omega : (1 : Int) < (p : Int))]; simp
      exact Int.dvd_of_emod_eq_zero h2
    have hmod : (p : Int) ∣ ((Xf t : Int) - Xnum t * (invD t : Int)) := by
      rw [hXf_cast]
      exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, Int.emod_emod, Int.sub_self, Int.zero_emod])
    obtain ⟨k1, hk1⟩ := hinv
    obtain ⟨k2, hk2⟩ := hmod
    exact ⟨(denom t : Int) * k2 + Xnum t * k1, by grind⟩
  have hDY : ∀ t, ¬ p ∣ denom t → (p : Int) ∣ ((denom t : Int) * (Yf t : Int) - Ynum t) := by
    intro t ht
    have hinv : (p : Int) ∣ ((denom t : Int) * (invD t : Int) - 1) := by
      have h1 : ((denom t * invD t : Nat) : Int) % (p : Int) = 1 := by exact_mod_cast hinvD t ht
      have h2 : ((denom t : Int) * (invD t : Int) - 1) % (p : Int) = 0 := by
        rw [Int.sub_emod]; push_cast at h1; rw [h1, Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 1) (by omega : (1 : Int) < (p : Int))]; simp
      exact Int.dvd_of_emod_eq_zero h2
    have hmod : (p : Int) ∣ ((Yf t : Int) - Ynum t * (invD t : Int)) := by
      rw [hYf_cast]
      exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, Int.emod_emod, Int.sub_self, Int.zero_emod])
    obtain ⟨k1, hk1⟩ := hinv
    obtain ⟨k2, hk2⟩ := hmod
    exact ⟨(denom t : Int) * k2 + Ynum t * k1, by grind⟩
  -- Property 1: (Xf t)^2 + 3 * (Yf t)^2 ≡ 4 * c (mod p)
  have hpt : ∀ t, ¬ p ∣ denom t → ((Xf t) ^ 2 + 3 * (Yf t) ^ 2) % p = (4 * c) % p := by
    intro t ht
    obtain ⟨kx, hkx⟩ := hDX t ht
    obtain ⟨ky, hky⟩ := hDY t ht
    have hpt0Z : (p : Int) ∣ ((X0 : Int) ^ 2 + 3 * (Y0 : Int) ^ 2 - 4 * (c : Int)) := by
      have h1 : (((X0 ^ 2 + 3 * Y0 ^ 2 : Nat) : Int) - ((4 * c : Nat) : Int)) % (p : Int) = 0 := by
        rw [Int.sub_emod]
        have : ((X0 ^ 2 + 3 * Y0 ^ 2 : Nat) : Int) % (p : Int) = ((4 * c : Nat) : Int) % (p : Int) := by
          exact_mod_cast hpt0
        rw [this, Int.sub_self, Int.zero_emod]
      have h2 : ((X0 ^ 2 + 3 * Y0 ^ 2 : Nat) : Int) - ((4 * c : Nat) : Int) =
                (X0 : Int) ^ 2 + 3 * (Y0 : Int) ^ 2 - 4 * (c : Int) := by push_cast; rfl
      rw [← h2]; exact Int.dvd_of_emod_eq_zero h1
    obtain ⟨k0, hk0⟩ := hpt0Z
    have hdvd_mul : (p : Int) ∣ ((denom t : Int) ^ 2 * (((Xf t : Int) ^ 2 + 3 * (Yf t : Int) ^ 2) - 4 * (c : Int))) := by
      have hx' : ((t.val : Int) ^ 2 + 3) * (Xf t : Int) - ((X0 : Int) * ((t.val : Int) ^ 2 - 3) - 6 * (Y0 : Int) * (t.val : Int)) = (p : Int) * kx := by
        dsimp only [Xnum, denom] at hkx; push_cast at hkx; exact hkx
      have hy' : ((t.val : Int) ^ 2 + 3) * (Yf t : Int) - ((Y0 : Int) * (3 - (t.val : Int) ^ 2) - 2 * (X0 : Int) * (t.val : Int)) = (p : Int) * ky := by
        dsimp only [Ynum, denom] at hky; push_cast at hky; exact hky
      have := stereo_pt_id X0 Y0 t.val (Xf t) (Yf t) c p kx ky k0 hx' hy' hk0
      dsimp only [denom]; push_cast; exact ⟨_, this⟩
    have hnd_d2 : ¬ p ∣ (denom t) ^ 2 := fun h => by
      rw [Nat.pow_two] at h
      rcases prime_dvd_mul hp h with h1 | h1 <;> exact ht h1
    -- Cancel (denom t)^2 mod p
    have hdvdZ : (p : Int) ∣ ((Xf t : Int) ^ 2 + 3 * (Yf t : Int) ^ 2 - 4 * (c : Int)) := by
      have hcop := coprime_of_prime_not_dvd hp hnd_d2
      obtain ⟨rx, ry, hr⟩ := exists_bezout p ((denom t) ^ 2)
      rw [hcop] at hr
      obtain ⟨q, hq⟩ := hdvd_mul
      exact ⟨((Xf t : Int) ^ 2 + 3 * (Yf t : Int) ^ 2 - 4 * (c : Int)) * rx + q * ry,
             int_cancel_coprime p ((denom t : Int) ^ 2) _ rx ry q (by push_cast at hr; exact hr) hq⟩
    have hmodZ : (((Xf t) ^ 2 + 3 * (Yf t) ^ 2 : Nat) : Int) % (p : Int) = ((4 * c : Nat) : Int) % (p : Int) := by
      obtain ⟨q, hq⟩ := hdvdZ
      have : (((Xf t) ^ 2 + 3 * (Yf t) ^ 2 : Nat) : Int) = ((4 * c : Nat) : Int) + (p : Int) * q := by
        push_cast; omega
      rw [this, Int.add_mul_emod_self_left]
    exact_mod_cast hmodZ
  -- Property 2: Injectivity of t ↦ (Xf t, Yf t) on ¬ p ∣ denom t
  have hinj_stereo : ∀ t1 t2 : Fin p, ¬ p ∣ denom t1 → ¬ p ∣ denom t2 →
      Xf t1 = Xf t2 → Yf t1 = Yf t2 → t1 = t2 := by
    intro t1 t2 ht1 ht2 hXeq hYeq
    obtain ⟨kx1, hkx1⟩ := hDX t1 ht1
    obtain ⟨ky1, hky1⟩ := hDY t1 ht1
    obtain ⟨kx2, hkx2⟩ := hDX t2 ht2
    obtain ⟨ky2, hky2⟩ := hDY t2 ht2
    have hpt0Z : (p : Int) ∣ ((X0 : Int) ^ 2 + 3 * (Y0 : Int) ^ 2 - 4 * (c : Int)) := by
      have h1 : (((X0 ^ 2 + 3 * Y0 ^ 2 : Nat) : Int) - ((4 * c : Nat) : Int)) % (p : Int) = 0 := by
        rw [Int.sub_emod]
        have : ((X0 ^ 2 + 3 * Y0 ^ 2 : Nat) : Int) % (p : Int) = ((4 * c : Nat) : Int) % (p : Int) := by
          exact_mod_cast hpt0
        rw [this, Int.sub_self, Int.zero_emod]
      have h2 : ((X0 ^ 2 + 3 * Y0 ^ 2 : Nat) : Int) - ((4 * c : Nat) : Int) =
                (X0 : Int) ^ 2 + 3 * (Y0 : Int) ^ 2 - 4 * (c : Int) := by push_cast; rfl
      rw [← h2]; exact Int.dvd_of_emod_eq_zero h1
    obtain ⟨k0, hk0⟩ := hpt0Z
    -- Let A = X0*(Xf - X0) - 3*Y0*(Yf + Y0), B = Y0*(Xf - X0) + X0*(Yf + Y0)
    -- Then denom(t) * A ≡ -24*c (mod p) and denom(t) * B ≡ -8*c*t (mod p),
    -- so 3 * B ≡ t * A (mod p), hence (t1 - t2) * (-24*c) ≡ 0 (mod p)!
    have hdvd_t : (p : Int) ∣ ((denom t2 : Int) * (24 * (c : Int)) * ((t1.val : Int) - (t2.val : Int))) := by
      let A1 : Int := (X0 : Int) * ((Xf t1 : Int) - (X0 : Int)) - 3 * (Y0 : Int) * ((Yf t1 : Int) + (Y0 : Int))
      let B1 : Int := (Y0 : Int) * ((Xf t1 : Int) - (X0 : Int)) + (X0 : Int) * ((Yf t1 : Int) + (Y0 : Int))
      have hA1 : (p : Int) ∣ ((denom t1 : Int) * A1 + 24 * (c : Int)) := by
        refine ⟨(X0 : Int) * kx1 - 3 * (Y0 : Int) * ky1 - 6 * k0, ?_⟩
        have hx1' : ((t1.val : Int) ^ 2 + 3) * (Xf t1 : Int) - ((X0 : Int) * ((t1.val : Int) ^ 2 - 3) - 6 * (Y0 : Int) * (t1.val : Int)) = (p : Int) * kx1 := by
          dsimp only [Xnum, denom] at hkx1; push_cast at hkx1; exact hkx1
        have hy1' : ((t1.val : Int) ^ 2 + 3) * (Yf t1 : Int) - ((Y0 : Int) * (3 - (t1.val : Int) ^ 2) - 2 * (X0 : Int) * (t1.val : Int)) = (p : Int) * ky1 := by
          dsimp only [Ynum, denom] at hky1; push_cast at hky1; exact hky1
        have := stereo_A_id X0 Y0 t1.val (Xf t1) (Yf t1) c p kx1 ky1 k0 hx1' hy1' hk0
        dsimp only [A1, denom]; push_cast; exact this
      have hB1 : (p : Int) ∣ ((denom t1 : Int) * B1 + 8 * (c : Int) * (t1.val : Int)) := by
        refine ⟨(Y0 : Int) * kx1 + (X0 : Int) * ky1 - 2 * (t1.val : Int) * k0, ?_⟩
        have hx1' : ((t1.val : Int) ^ 2 + 3) * (Xf t1 : Int) - ((X0 : Int) * ((t1.val : Int) ^ 2 - 3) - 6 * (Y0 : Int) * (t1.val : Int)) = (p : Int) * kx1 := by
          dsimp only [Xnum, denom] at hkx1; push_cast at hkx1; exact hkx1
        have hy1' : ((t1.val : Int) ^ 2 + 3) * (Yf t1 : Int) - ((Y0 : Int) * (3 - (t1.val : Int) ^ 2) - 2 * (X0 : Int) * (t1.val : Int)) = (p : Int) * ky1 := by
          dsimp only [Ynum, denom] at hky1; push_cast at hky1; exact hky1
        have := stereo_B_id X0 Y0 t1.val (Xf t1) (Yf t1) c p kx1 ky1 k0 hx1' hy1' hk0
        dsimp only [B1, denom]; push_cast; exact this
      have hA2 : (p : Int) ∣ ((denom t2 : Int) * A1 + 24 * (c : Int)) := by
        refine ⟨(X0 : Int) * kx2 - 3 * (Y0 : Int) * ky2 - 6 * k0, ?_⟩
        have hx2' : ((t2.val : Int) ^ 2 + 3) * (Xf t2 : Int) - ((X0 : Int) * ((t2.val : Int) ^ 2 - 3) - 6 * (Y0 : Int) * (t2.val : Int)) = (p : Int) * kx2 := by
          dsimp only [Xnum, denom] at hkx2; push_cast at hkx2; exact hkx2
        have hy2' : ((t2.val : Int) ^ 2 + 3) * (Yf t2 : Int) - ((Y0 : Int) * (3 - (t2.val : Int) ^ 2) - 2 * (X0 : Int) * (t2.val : Int)) = (p : Int) * ky2 := by
          dsimp only [Ynum, denom] at hky2; push_cast at hky2; exact hky2
        have := stereo_A_id X0 Y0 t2.val (Xf t2) (Yf t2) c p kx2 ky2 k0 hx2' hy2' hk0
        dsimp only [A1, denom]; rw [hXeq, hYeq]; push_cast; exact this
      have hB2 : (p : Int) ∣ ((denom t2 : Int) * B1 + 8 * (c : Int) * (t2.val : Int)) := by
        refine ⟨(Y0 : Int) * kx2 + (X0 : Int) * ky2 - 2 * (t2.val : Int) * k0, ?_⟩
        have hx2' : ((t2.val : Int) ^ 2 + 3) * (Xf t2 : Int) - ((X0 : Int) * ((t2.val : Int) ^ 2 - 3) - 6 * (Y0 : Int) * (t2.val : Int)) = (p : Int) * kx2 := by
          dsimp only [Xnum, denom] at hkx2; push_cast at hkx2; exact hkx2
        have hy2' : ((t2.val : Int) ^ 2 + 3) * (Yf t2 : Int) - ((Y0 : Int) * (3 - (t2.val : Int) ^ 2) - 2 * (X0 : Int) * (t2.val : Int)) = (p : Int) * ky2 := by
          dsimp only [Ynum, denom] at hky2; push_cast at hky2; exact hky2
        have := stereo_B_id X0 Y0 t2.val (Xf t2) (Yf t2) c p kx2 ky2 k0 hx2' hy2' hk0
        dsimp only [B1, denom]; rw [hXeq, hYeq]; push_cast; exact this
      obtain ⟨qa1, hqa1⟩ := hA1
      obtain ⟨qb1, hqb1⟩ := hB1
      obtain ⟨qa2, hqa2⟩ := hA2
      obtain ⟨qb2, hqb2⟩ := hB2
      exact ⟨_, stereo_elim_id (denom t1) (denom t2) A1 B1 c t1.val t2.val p qa1 qb1 qa2 qb2 hqa1 hqb1 hqa2 hqb2⟩
    -- Cancel denom t2 and 24*c (both coprime to p since p ≥ 17 and ¬ p ∣ c)
    have hnd24 : ¬ p ∣ 24 := fun h => by
      have : 24 = 2 * (2 * (2 * 3)) := rfl
      rw [this] at h
      rcases prime_dvd_mul hp h with h2 | h12
      · exact hnd2 h2
      · rcases prime_dvd_mul hp h12 with h2 | h6
        · exact hnd2 h2
        · rcases prime_dvd_mul hp h6 with h2 | h3
          · exact hnd2 h2
          · exact hnd3 h3
    have hnd_coeff : ¬ p ∣ (denom t2 * (24 * c)) := fun h => by
      rcases prime_dvd_mul hp h with h1 | h2
      · exact ht2 h1
      · rcases prime_dvd_mul hp h2 with h24 | hc
        · exact hnd24 h24
        · exact hndc hc
    have hcop := coprime_of_prime_not_dvd hp hnd_coeff
    obtain ⟨rx, ry, hr⟩ := exists_bezout p (denom t2 * (24 * c))
    rw [hcop] at hr
    obtain ⟨q, hq⟩ := hdvd_t
    have hdvd_diff : (p : Int) ∣ ((t1.val : Int) - (t2.val : Int)) := by
      have hq' : ((denom t2 * (24 * c) : Nat) : Int) * ((t1.val : Int) - (t2.val : Int)) = (p : Int) * q := by
        push_cast; exact hq
      exact ⟨((t1.val : Int) - (t2.val : Int)) * rx + q * ry,
             int_cancel_coprime p ((denom t2 * (24 * c) : Nat) : Int) _ rx ry q (by push_cast at hr; exact hr) hq'⟩
    obtain ⟨k, hk⟩ := hdvd_diff
    have ht1Z : (t1.val : Int) < (p : Int) := by exact_mod_cast t1.isLt
    have ht2Z : (t2.val : Int) < (p : Int) := by exact_mod_cast t2.isLt
    have hk0 : k = 0 := by
      rcases Int.lt_trichotomy k 0 with hlt | heq | hgt
      · have hle : (p : Int) * k ≤ -(p : Int) := by
          have : k ≤ -1 := by omega
          have hmul := Int.mul_le_mul_of_nonneg_left this (show (0 : Int) ≤ (p : Int) by omega)
          simp only [Int.mul_neg, Int.mul_one] at hmul
          exact hmul
        omega
      · exact heq
      · have hge : (p : Int) ≤ (p : Int) * k := by
          have : 1 ≤ k := by omega
          have hmul := Int.mul_le_mul_of_nonneg_left this (show (0 : Int) ≤ (p : Int) by omega)
          simp only [Int.mul_one] at hmul
          exact hmul
        omega
    rw [hk0, Int.mul_zero] at hk
    exact Fin.ext (by omega)
  -- Now bound the 5 bad sets of t : Fin p:
  -- Bad 1: p ∣ denom t (i.e. t^2 ≡ p - 3 (mod p)) → at most 2 values
  obtain ⟨L1, hL1_len, hL1⟩ := at_most_two_of_sq hp (fun t => p ∣ denom t) (fun t => t.val)
    (fun t _ => t.isLt) (fun _ _ _ _ h => Fin.ext h) (p - 3) (fun t ht => by
      obtain ⟨k, hk⟩ := ht
      have h1 : t.val ^ 2 + 3 = p * k := hk
      have hmod : ((t.val ^ 2 : Nat) : Int) % (p : Int) = ((p - 3 : Nat) : Int) % (p : Int) := by
        have h1Z : ((t.val ^ 2 : Nat) : Int) + 3 = (p : Int) * (k : Int) := by exact_mod_cast h1
        have hp3 : ((p - 3 : Nat) : Int) = (p : Int) - 3 := Int.ofNat_sub (by omega)
        have : ((t.val ^ 2 : Nat) : Int) = ((p - 3 : Nat) : Int) + (p : Int) * ((k : Int) - 1) := by
          rw [hp3, Int.mul_sub, Int.mul_one]; omega
        rw [this, Int.add_mul_emod_self_left]
      exact_mod_cast hmod)
  -- Helper: modular inverse of 3 mod p
  obtain ⟨inv3, hinv3_lt, hinv3⟩ := exists_mod_inv hp_pos (by rw [Nat.gcd_comm]; exact coprime_of_prime_not_dvd hp hnd3)
  rw [Nat.mod_eq_of_lt (by omega : 1 < p)] at hinv3
  -- Bad 2: ¬ p ∣ denom t ∧ Xf t = 0 (implies (Yf t)^2 ≡ 4*c*inv3 (mod p)) → at most 2 values
  obtain ⟨L2, hL2_len, hL2⟩ := at_most_two_of_sq hp (fun t => ¬ p ∣ denom t ∧ Xf t = 0) Yf
    (fun t _ => hYf_lt t)
    (fun t1 t2 h1 h2 hY => hinj_stereo t1 t2 h1.1 h2.1 (by rw [h1.2, h2.2]) hY)
    (4 * c * inv3) (fun t ht => by
      have hcon := hpt t ht.1
      rw [ht.2] at hcon
      simp only [Nat.zero_pow (by omega : 0 < 2), Nat.zero_add] at hcon
      have : (Yf t ^ 2) % p = (3 * inv3 * Yf t ^ 2) % p := by
        rw [Nat.mul_mod, hinv3, Nat.one_mul, Nat.mod_mod]
      rw [this]
      have hcomm : 3 * inv3 * Yf t ^ 2 = (3 * Yf t ^ 2) * inv3 := by grind
      rw [hcomm, Nat.mul_mod, hcon, ← Nat.mul_mod])
  -- Bad 3: ¬ p ∣ denom t ∧ Yf t = 0 (implies (Xf t)^2 ≡ 4*c (mod p)) → at most 2 values
  obtain ⟨L3, hL3_len, hL3⟩ := at_most_two_of_sq hp (fun t => ¬ p ∣ denom t ∧ Yf t = 0) Xf
    (fun t _ => hXf_lt t)
    (fun t1 t2 h1 h2 hX => hinj_stereo t1 t2 h1.1 h2.1 hX (by rw [h1.2, h2.2]))
    (4 * c) (fun t ht => by
      have hcon := hpt t ht.1
      rw [ht.2] at hcon
      simp only [Nat.zero_pow (by omega : 0 < 2), Nat.mul_zero, Nat.add_zero] at hcon
      exact hcon)
  -- Bad 4: ¬ p ∣ denom t ∧ (Xf t = Yf t ∨ Xf t + Yf t = p) (implies Xf^2 ≡ c and Yf^2 ≡ c) → at most 4 values
  have hnd4 : ¬ p ∣ 4 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  obtain ⟨inv4, hinv4_lt, hinv4⟩ := exists_mod_inv hp_pos (by rw [Nat.gcd_comm]; exact coprime_of_prime_not_dvd hp hnd4)
  rw [Nat.mod_eq_of_lt (by omega : 1 < p)] at hinv4
  obtain ⟨L4, hL4_len, hL4⟩ := at_most_four_of_pair_sq hp
    (fun t => ¬ p ∣ denom t ∧ (Xf t = Yf t ∨ Xf t + Yf t = p)) Xf Yf
    (fun t _ => hXf_lt t) (fun t _ => hYf_lt t)
    (fun t1 t2 h1 h2 hX hY => hinj_stereo t1 t2 h1.1 h2.1 hX hY)
    c c
    (fun t ht => by
      have hcon := hpt t ht.1
      have hsqEq : (Yf t) ^ 2 % p = (Xf t) ^ 2 % p := by
        rcases ht.2 with hEq | hSum
        · rw [hEq]
        · have hZ : (((Yf t : Int) ^ 2 - (Xf t : Int) ^ 2) % (p : Int)) = 0 := by
            have : (Yf t : Int) ^ 2 - (Xf t : Int) ^ 2 = (p : Int) * ((Yf t : Int) - (Xf t : Int)) := by
              have : (Xf t : Int) + (Yf t : Int) = (p : Int) := by exact_mod_cast hSum
              grind
            rw [this, Int.mul_emod_right]
          have hmodZ : ((Yf t : Int) ^ 2) % (p : Int) = ((Xf t : Int) ^ 2) % (p : Int) := by
            obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hZ
            have : (Yf t : Int) ^ 2 = (Xf t : Int) ^ 2 + (p : Int) * q := by omega
            rw [this, Int.add_mul_emod_self_left]
          exact_mod_cast hmodZ
      have h4X : (4 * Xf t ^ 2) % p = (4 * c) % p := by
        have : (Xf t ^ 2 + 3 * Yf t ^ 2) % p = (4 * Xf t ^ 2) % p := by
          rw [Nat.add_mod, Nat.mul_mod 3, hsqEq, ← Nat.mul_mod 3, ← Nat.add_mod]
          have : Xf t ^ 2 + 3 * Xf t ^ 2 = 4 * Xf t ^ 2 := by omega
          rw [this]
        rw [← this]; exact hcon
      have : Xf t ^ 2 % p = (4 * inv4 * Xf t ^ 2) % p := by
        rw [Nat.mul_mod, hinv4, Nat.one_mul, Nat.mod_mod]
      rw [this]
      have h1 : 4 * inv4 * Xf t ^ 2 = (4 * Xf t ^ 2) * inv4 := by grind
      have h2 : c % p = ((4 * c) * inv4) % p := by
        have : (4 * c) * inv4 = (4 * inv4) * c := by grind
        rw [this, Nat.mul_mod, hinv4, Nat.one_mul, Nat.mod_mod]
      rw [h1, Nat.mul_mod, h4X, ← Nat.mul_mod, ← h2])
    (fun t ht => by
      have hcon := hpt t ht.1
      have hsqEq : (Xf t) ^ 2 % p = (Yf t) ^ 2 % p := by
        rcases ht.2 with hEq | hSum
        · rw [hEq]
        · have hZ : (((Xf t : Int) ^ 2 - (Yf t : Int) ^ 2) % (p : Int)) = 0 := by
            have : (Xf t : Int) ^ 2 - (Yf t : Int) ^ 2 = (p : Int) * ((Xf t : Int) - (Yf t : Int)) := by
              have : (Xf t : Int) + (Yf t : Int) = (p : Int) := by exact_mod_cast hSum
              grind
            rw [this, Int.mul_emod_right]
          have hmodZ : ((Xf t : Int) ^ 2) % (p : Int) = ((Yf t : Int) ^ 2) % (p : Int) := by
            obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hZ
            have : (Xf t : Int) ^ 2 = (Yf t : Int) ^ 2 + (p : Int) * q := by omega
            rw [this, Int.add_mul_emod_self_left]
          exact_mod_cast hmodZ
      have h4Y : (4 * Yf t ^ 2) % p = (4 * c) % p := by
        have : (Xf t ^ 2 + 3 * Yf t ^ 2) % p = (4 * Yf t ^ 2) % p := by
          rw [Nat.add_mod, hsqEq, ← Nat.add_mod]
          have : Yf t ^ 2 + 3 * Yf t ^ 2 = 4 * Yf t ^ 2 := by omega
          rw [this]
        rw [← this]; exact hcon
      have : Yf t ^ 2 % p = (4 * inv4 * Yf t ^ 2) % p := by
        rw [Nat.mul_mod, hinv4, Nat.one_mul, Nat.mod_mod]
      rw [this]
      have h1 : 4 * inv4 * Yf t ^ 2 = (4 * Yf t ^ 2) * inv4 := by grind
      have h2 : c % p = ((4 * c) * inv4) % p := by
        have : (4 * c) * inv4 = (4 * inv4) * c := by grind
        rw [this, Nat.mul_mod, hinv4, Nat.one_mul, Nat.mod_mod]
      rw [h1, Nat.mul_mod, h4Y, ← Nat.mul_mod, ← h2])
  -- Bad 5: ¬ p ∣ denom t ∧ (3 * (Yf t)^2) % p = c % p (implies Xf^2 ≡ 3*c and Yf^2 ≡ c*inv3) → at most 4 values
  obtain ⟨L5, hL5_len, hL5⟩ := at_most_four_of_pair_sq hp
    (fun t => ¬ p ∣ denom t ∧ (3 * (Yf t) ^ 2) % p = c % p) Xf Yf
    (fun t _ => hXf_lt t) (fun t _ => hYf_lt t)
    (fun t1 t2 h1 h2 hX hY => hinj_stereo t1 t2 h1.1 h2.1 hX hY)
    (3 * c) (c * inv3)
    (fun t ht => by
      have hcon := hpt t ht.1
      have hZ : (((Xf t : Int) ^ 2 - 3 * (c : Int)) % (p : Int)) = 0 := by
        have h1 : (((Xf t : Int) ^ 2 + 3 * (Yf t : Int) ^ 2) - 4 * (c : Int)) % (p : Int) = 0 := by
          rw [Int.sub_emod]
          have : ((Xf t ^ 2 + 3 * Yf t ^ 2 : Nat) : Int) % (p : Int) = ((4 * c : Nat) : Int) % (p : Int) := by
            exact_mod_cast hcon
          push_cast at this; rw [this, Int.sub_self, Int.zero_emod]
        have h2 : ((3 * (Yf t : Int) ^ 2) - (c : Int)) % (p : Int) = 0 := by
          rw [Int.sub_emod]
          have : ((3 * Yf t ^ 2 : Nat) : Int) % (p : Int) = (c : Int) % (p : Int) := by exact_mod_cast ht.2
          push_cast at this; rw [this, Int.sub_self, Int.zero_emod]
        obtain ⟨q1, hq1⟩ := Int.dvd_of_emod_eq_zero h1
        obtain ⟨q2, hq2⟩ := Int.dvd_of_emod_eq_zero h2
        have : (Xf t : Int) ^ 2 - 3 * (c : Int) = (p : Int) * (q1 - q2) := by grind
        rw [this, Int.mul_emod_right]
      have hmodZ : ((Xf t : Int) ^ 2) % (p : Int) = ((3 * c : Nat) : Int) % (p : Int) := by
        obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hZ
        have : (Xf t : Int) ^ 2 = ((3 * c : Nat) : Int) + (p : Int) * q := by push_cast; omega
        rw [this, Int.add_mul_emod_self_left]
      exact_mod_cast hmodZ)
    (fun t ht => by
      have : Yf t ^ 2 % p = (3 * inv3 * Yf t ^ 2) % p := by
        rw [Nat.mul_mod, hinv3, Nat.one_mul, Nat.mod_mod]
      rw [this]
      have h1 : 3 * inv3 * Yf t ^ 2 = (3 * Yf t ^ 2) * inv3 := by grind
      rw [h1, Nat.mul_mod, ht.2, ← Nat.mul_mod])
  -- Pick t : Fin p avoiding L1 ++ L2 ++ L3 ++ L4 ++ L5 (length ≤ 14 < 17 ≤ p)!
  let L := L1 ++ L2 ++ L3 ++ L4 ++ L5
  have hL_lt : L.length < p := by
    have : L.length = L1.length + L2.length + L3.length + L4.length + L5.length := by
      simp only [L, List.length_append]
    omega
  obtain ⟨t, ht_not_in⟩ := exists_not_in_list L hL_lt
  have hnot1 : ¬ p ∣ denom t := fun h => ht_not_in (by simp [L, hL1 t h])
  have hnot2 : Xf t ≠ 0 := fun h => ht_not_in (by simp [L, hL2 t ⟨hnot1, h⟩])
  have hnot3 : Yf t ≠ 0 := fun h => ht_not_in (by simp [L, hL3 t ⟨hnot1, h⟩])
  have hnot4 : Xf t ≠ Yf t ∧ Xf t + Yf t ≠ p :=
    ⟨fun h => ht_not_in (by simp [L, hL4 t ⟨hnot1, Or.inl h⟩]),
     fun h => ht_not_in (by simp [L, hL4 t ⟨hnot1, Or.inr h⟩])⟩
  have hnot5 : (3 * (Yf t) ^ 2) % p ≠ c % p := fun h => ht_not_in (by simp [L, hL5 t ⟨hnot1, h⟩])
  -- Fold (Xf t, Yf t) into [1, (p - 1) / 2]^2!
  let X := if Xf t ≤ (p - 1) / 2 then Xf t else p - Xf t
  let Y := if Yf t ≤ (p - 1) / 2 then Yf t else p - Yf t
  have hXf_lt_t := hXf_lt t
  have hYf_lt_t := hYf_lt t
  have hX_range : 1 ≤ X ∧ X ≤ (p - 1) / 2 := by dsimp only [X]; split <;> omega
  have hY_range : 1 ≤ Y ∧ Y ≤ (p - 1) / 2 := by dsimp only [Y]; split <;> omega
  have hXY_ne : X ≠ Y := by dsimp only [X, Y]; split <;> split <;> omega
  have hX_sq : X ^ 2 % p = (Xf t) ^ 2 % p := by
    dsimp only [X]
    split
    · rfl
    · have hZ : (((p - Xf t : Nat) : Int) ^ 2 - (Xf t : Int) ^ 2) % (p : Int) = 0 := by
        have hsub : ((p - Xf t : Nat) : Int) = (p : Int) - (Xf t : Int) := Int.ofNat_sub (by omega)
        rw [hsub]
        have : ((p : Int) - (Xf t : Int)) ^ 2 - (Xf t : Int) ^ 2 = (p : Int) * ((p : Int) - 2 * (Xf t : Int)) := by grind
        rw [this, Int.mul_emod_right]
      have hmodZ : (((p - Xf t : Nat) : Int) ^ 2) % (p : Int) = ((Xf t : Int) ^ 2) % (p : Int) := by
        obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hZ
        have : ((p - Xf t : Nat) : Int) ^ 2 = (Xf t : Int) ^ 2 + (p : Int) * q := by omega
        rw [this, Int.add_mul_emod_self_left]
      exact_mod_cast hmodZ
  have hY_sq : Y ^ 2 % p = (Yf t) ^ 2 % p := by
    dsimp only [Y]
    split
    · rfl
    · have hZ : (((p - Yf t : Nat) : Int) ^ 2 - (Yf t : Int) ^ 2) % (p : Int) = 0 := by
        have hsub : ((p - Yf t : Nat) : Int) = (p : Int) - (Yf t : Int) := Int.ofNat_sub (by omega)
        rw [hsub]
        have : ((p : Int) - (Yf t : Int)) ^ 2 - (Yf t : Int) ^ 2 = (p : Int) * ((p : Int) - 2 * (Yf t : Int)) := by grind
        rw [this, Int.mul_emod_right]
      have hmodZ : (((p - Yf t : Nat) : Int) ^ 2) % (p : Int) = ((Yf t : Int) ^ 2) % (p : Int) := by
        obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hZ
        have : ((p - Yf t : Nat) : Int) ^ 2 = (Yf t : Int) ^ 2 + (p : Int) * q := by omega
        rw [this, Int.add_mul_emod_self_left]
      exact_mod_cast hmodZ
  have hXY_conic : (X ^ 2 + 3 * Y ^ 2) % p = (4 * c) % p := by
    rw [Nat.add_mod, hX_sq, Nat.mul_mod 3, hY_sq, ← Nat.mul_mod 3, ← Nat.add_mod]
    exact hpt t hnot1
  have h3Y2_ne : (3 * Y ^ 2) % p ≠ c % p := by
    rw [Nat.mul_mod 3, hY_sq, ← Nat.mul_mod 3]; exact hnot5
  exact conicBox_from_XY hp_odd (by omega) hinv4 hX_range hY_range hXY_ne hXY_conic h3Y2_ne


/-! ### Section 6: From ConicBox to Collisions, Base Tables, and Large-d Tables -/

/-- Witness table checker for ConicBox p e (verified by kernel `decide`). -/
def checkConicTable (p q : Nat) (tab : Array (Nat × Nat)) : Bool :=
  tab.size == q &&
  (List.range q).all fun c =>
    if c % p == 0 then true
    else
      let (u, v) := tab[c]!
      1 ≤ u && u < v && v ≤ (q - 1) / 2 &&
      (u * u + u * v + v * v) % q == c &&
      (2 * u + v) % p != 0 && (u + 2 * v) % p != 0

theorem conicBox_of_table {p e : Nat} (hp : 0 < p) (he : 1 ≤ e) (tab : Array (Nat × Nat))
    (hcheck : checkConicTable p (p ^ e) tab = true) : ConicBox p e := by
  intro c hndc
  have hq_pos : 0 < p ^ e := Nat.pow_pos hp
  have hc_lt : c % p ^ e < p ^ e := Nat.mod_lt c hq_pos
  unfold checkConicTable at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hcheck
  have hrow := hcheck.2 (c % p ^ e) hc_lt
  have hnd_mod : (c % p ^ e) % p ≠ 0 := by
    intro h0
    apply hndc
    have hpe_dvd : p ∣ p ^ e := by
      cases e with
      | zero => omega
      | succ k => exact ⟨p ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    obtain ⟨a, ha⟩ := hpe_dvd
    have hdiv := Nat.div_add_mod c (p ^ e)
    obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero h0
    refine ⟨a * (c / p ^ e) + b, ?_⟩
    have : p ^ e * (c / p ^ e) = p * (a * (c / p ^ e)) := by rw [ha, Nat.mul_assoc]
    rw [Nat.mul_add, ← this, ← hb]; omega
  rw [ite_eq_right (by simp [hnd_mod])] at hrow
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at hrow
  let uv := tab[c % p ^ e]!
  refine ⟨uv.1, uv.2, hrow.1.1.1.1.1, hrow.1.1.1.1.2, hrow.1.1.1.2, ?_, ?_, ?_⟩
  · have hsq : uv.1 ^ 2 = uv.1 * uv.1 := Nat.pow_two uv.1
    have hsq2 : uv.2 ^ 2 = uv.2 * uv.2 := Nat.pow_two uv.2
    rw [hsq, hsq2]; exact hrow.1.1.2
  · intro hdvd; exact hrow.1.2 (Nat.mod_eq_zero_of_dvd hdvd)
  · intro hdvd; exact hrow.2 (Nat.mod_eq_zero_of_dvd hdvd)

def tab_5_3 : Array (Nat × Nat) := #[
  (0,0), (4,56), (3,28), (4,44), (3,32), (0,0), (1,19), (8,43), (1,11), (2,15),
  (0,0), (1,35), (3,18), (6,16), (2,55), (0,0), (1,40), (8,58), (4,14), (2,3),
  (0,0), (1,4), (17,22), (1,16), (2,38), (0,0), (1,25), (7,12), (1,51), (2,48),
  (0,0), (1,5), (2,22), (1,61), (2,33), (0,0), (1,60), (2,27), (1,46), (2,5),
  (0,0), (1,59), (8,33), (1,6), (2,53), (0,0), (1,20), (2,12), (6,36), (2,35),
  (0,0), (1,50), (7,37), (6,46), (2,25), (0,0), (1,30), (2,47), (4,34), (2,40),
  (0,0), (1,39), (2,52), (4,24), (2,43), (0,0), (1,34), (2,7), (1,56), (2,20),
  (0,0), (1,45), (2,37), (14,19), (2,13), (0,0), (1,49), (2,17), (1,26), (2,23),
  (0,0), (1,55), (3,48), (1,36), (2,8), (0,0), (1,14), (7,47), (1,21), (2,30),
  (0,0), (1,9), (2,32), (9,59), (2,28), (0,0), (1,54), (2,62), (1,41), (2,60),
  (0,0), (1,24), (2,42), (6,21), (2,50), (0,0), (1,44), (3,23), (4,59), (2,58),
  (0,0), (1,10), (3,43), (4,49), (2,18), (0,0), (1,15), (2,57), (1,31), (2,45),
  (0,0), (1,29), (13,23), (6,61), (2,10)
]
def tab_7_3 : Array (Nat × Nat) := #[
  (0,0), (6,133), (3,161), (8,92), (5,107), (2,107), (3,17), (0,0), (1,41), (4,35),
  (6,153), (2,126), (9,44), (11,39), (0,0), (1,161), (3,60), (8,113), (2,154), (9,86),
  (25,95), (0,0), (1,76), (3,25), (1,106), (2,84), (2,86), (10,143), (0,0), (1,69),
  (3,105), (13,139), (2,82), (5,159), (3,31), (0,0), (1,160), (3,4), (8,22), (2,5),
  (9,114), (4,81), (0,0), (1,6), (3,18), (1,64), (2,26), (12,19), (3,136), (0,0),
  (1,49), (3,63), (13,34), (2,145), (2,58), (4,25), (0,0), (1,7), (3,95), (8,127),
  (2,19), (16,135), (4,144), (0,0), (1,132), (3,158), (6,69), (2,7), (5,47), (3,73),
  (0,0), (1,27), (3,123), (1,8), (2,61), (2,37), (17,87), (0,0), (1,20), (3,7),
  (6,97), (2,112), (9,72), (4,60), (0,0), (1,111), (3,102), (15,162), (2,152), (2,170),
  (3,157), (0,0), (1,42), (3,116), (6,76), (2,168), (9,156), (4,151), (0,0), (1,98),
  (3,32), (1,148), (2,49), (2,9), (3,66), (0,0), (1,56), (3,147), (1,85), (2,166),
  (5,40), (3,45), (0,0), (1,83), (3,84), (1,120), (2,138), (5,96), (4,165), (0,0),
  (1,21), (3,119), (15,92), (2,133), (5,54), (3,52), (0,0), (1,28), (3,88), (1,141),
  (2,33), (9,23), (3,80), (0,0), (1,62), (3,140), (1,127), (2,42), (2,121), (3,10),
  (0,0), (1,91), (3,126), (8,106), (2,21), (2,163), (11,144), (0,0), (1,147), (3,130),
  (1,50), (2,96), (12,75), (10,108), (0,0), (1,105), (3,49), (6,104), (2,28), (5,89),
  (4,95), (0,0), (1,34), (3,11), (1,22), (2,56), (5,145), (3,122), (0,0), (1,70),
  (3,21), (1,155), (2,12), (5,103), (10,45), (0,0), (1,77), (3,154), (1,43), (2,161),
  (2,128), (4,11), (0,0), (1,13), (3,42), (1,29), (2,103), (2,72), (17,143), (0,0),
  (1,140), (3,28), (1,113), (2,124), (2,114), (3,38), (0,0), (1,146), (3,112), (8,43),
  (2,98), (12,124), (3,115), (0,0), (1,154), (3,46), (13,97), (2,117), (2,149), (3,94),
  (0,0), (1,14), (3,109), (6,20), (2,89), (2,142), (4,116), (0,0), (1,119), (3,74),
  (1,57), (2,159), (5,152), (3,101), (0,0), (1,126), (3,56), (6,48), (2,14), (2,79),
  (3,129), (0,0), (1,35), (3,53), (20,48), (2,91), (2,23), (3,59), (0,0), (1,153),
  (3,67), (1,15), (2,70), (2,65), (11,95), (0,0), (1,97), (3,14), (6,41), (2,47),
  (5,33), (10,157), (0,0), (1,139), (3,144), (1,134), (2,77), (2,100), (4,46), (0,0),
  (1,63), (3,133), (1,169), (2,105), (2,93), (3,171), (0,0), (1,168), (3,168), (13,125),
  (2,35), (12,145), (10,94), (0,0), (1,167), (3,39), (6,146), (2,131), (2,30), (17,66),
  (0,0), (1,84), (3,151), (6,13), (2,54), (5,166), (4,130), (0,0), (1,104), (3,165),
  (6,125), (2,75), (2,16), (3,87), (0,0), (1,48), (3,81), (1,99), (2,147), (2,156),
  (3,164), (0,0), (1,90), (3,98), (1,36), (2,68), (2,51), (3,143), (0,0), (1,112),
  (3,35), (1,71), (2,40), (2,44), (3,24), (0,0), (1,125), (3,70), (15,43), (2,110),
  (2,135), (3,150), (0,0), (1,118), (3,137), (1,92), (2,63), (5,110), (4,109), (0,0),
  (1,133), (3,91), (1,78), (2,140), (9,163), (3,108), (0,0), (1,55), (3,77), (1,162),
  (2,119), (23,93), (10,31)
]
def tab_11_2 : Array (Nat × Nat) := #[
  (0,0), (10,12), (1,36), (5,44), (7,29), (3,14), (2,26), (1,2), (2,47), (5,49),
  (1,50), (0,0), (1,11), (1,3), (1,45), (2,53), (7,15), (2,15), (1,19), (2,3),
  (3,44), (1,4), (0,0), (1,22), (1,29), (6,16), (2,11), (4,33), (2,4), (1,41),
  (2,39), (3,30), (1,59), (0,0), (1,33), (1,58), (1,12), (2,42), (3,58), (2,5),
  (1,57), (2,36), (3,11), (1,6), (0,0), (1,44), (1,25), (1,56), (2,22), (4,18),
  (2,16), (1,35), (2,6), (3,55), (1,48), (0,0), (1,55), (1,7), (5,55), (2,31),
  (3,47), (2,27), (1,13), (2,50), (3,19), (1,17), (0,0), (1,54), (1,40), (1,23),
  (2,33), (4,44), (2,38), (1,8), (2,25), (3,22), (1,37), (0,0), (1,43), (1,47),
  (5,11), (2,20), (3,36), (2,49), (1,30), (2,17), (3,52), (1,28), (0,0), (1,32),
  (1,14), (5,6), (2,44), (4,7), (2,59), (1,52), (2,58), (3,8), (1,26), (0,0),
  (1,21), (1,18), (1,34), (2,9), (3,25), (2,48), (1,46), (2,14), (3,33), (1,39),
  (0,0), (1,10), (1,51), (5,50), (2,55), (4,55), (2,37), (1,24), (2,28), (3,41),
  (1,15)
]
def tab_13_2 : Array (Nat × Nat) := #[
  (0,0), (10,62), (2,69), (4,39), (6,19), (1,18), (2,60), (1,2), (1,34), (4,43),
  (5,57), (3,17), (5,65), (0,0), (1,13), (2,46), (9,17), (2,76), (1,72), (2,3),
  (1,62), (1,4), (3,49), (6,26), (3,71), (8,18), (0,0), (1,26), (2,4), (1,66),
  (2,13), (1,5), (2,68), (1,41), (1,43), (3,65), (5,70), (3,4), (5,60), (0,0),
  (1,39), (2,56), (1,14), (2,63), (1,83), (2,34), (1,23), (1,82), (3,13), (6,20),
  (3,82), (5,39), (0,0), (1,52), (2,59), (4,52), (2,26), (1,7), (2,29), (1,80),
  (1,47), (3,36), (5,83), (3,6), (2,67), (0,0), (1,65), (2,7), (1,79), (2,50),
  (1,70), (2,73), (1,15), (1,8), (3,78), (6,72), (3,69), (2,41), (0,0), (1,78),
  (2,43), (1,27), (2,39), (1,20), (2,8), (1,49), (1,30), (3,26), (6,65), (3,19),
  (2,15), (0,0), (1,77), (2,72), (4,61), (2,37), (1,57), (2,55), (1,54), (1,69),
  (3,23), (5,18), (3,56), (5,47), (0,0), (1,64), (2,20), (4,65), (2,52), (1,33),
  (2,47), (1,10), (1,60), (3,75), (6,13), (3,32), (5,52), (0,0), (1,51), (2,30),
  (1,40), (2,24), (1,44), (2,16), (1,75), (1,21), (3,39), (5,31), (3,43), (5,8),
  (0,0), (1,38), (2,82), (4,9), (2,65), (1,46), (2,81), (1,28), (1,17), (3,10),
  (6,33), (3,45), (2,80), (0,0), (1,25), (2,33), (4,48), (2,11), (1,31), (2,21),
  (1,36), (1,56), (3,62), (5,44), (3,30), (2,54), (0,0), (1,12), (2,17), (1,53),
  (2,78), (1,59), (2,42), (1,67), (1,73), (3,52), (6,78), (3,58), (2,28)
]

set_option maxRecDepth 4000 in
theorem base_5_3 : ConicBox 5 3 := conicBox_of_table (by omega) (by omega) tab_5_3 (by decide)
set_option maxRecDepth 4000 in
theorem base_7_3 : ConicBox 7 3 := conicBox_of_table (by omega) (by omega) tab_7_3 (by decide)
set_option maxRecDepth 4000 in
theorem base_11_2 : ConicBox 11 2 := conicBox_of_table (by omega) (by omega) tab_11_2 (by decide)
set_option maxRecDepth 4000 in
theorem base_13_2 : ConicBox 13 2 := conicBox_of_table (by omega) (by omega) tab_13_2 (by decide)

/-- Witness table checker for large-d small-prime collisions (q in {5, 25, 7, 49, 11, 13}). -/
def checkLargeDTable (p q : Nat) (tab : Array (Nat × Nat)) : Bool :=
  tab.size == q &&
  (List.range q).all fun d0 =>
    if d0 % p == 0 then true
    else
      let (x, t) := tab[d0]!
      1 ≤ x && x ≤ q && 1 ≤ t && t ≤ (q - 1) / 2 &&
      (2 * (x * x + x * (x + t * d0) + (x + t * d0) * (x + t * d0)) + 1) % q == 0

def ld_5 : Array (Nat × Nat) := #[
  (0,0), (1,1), (2,2), (1,2), (2,1)
]
def ld_25 : Array (Nat × Nat) := #[
  (0,0), (3,1), (4,2), (21,2), (4,1), (0,0), (21,1), (4,2), (13,2), (4,1),
  (0,0), (18,1), (4,2), (3,2), (4,1), (0,0), (13,1), (4,2), (18,2), (2,1),
  (0,0), (8,1), (2,2), (8,2), (4,1)
]
def ld_7 : Array (Nat × Nat) := #[
  (0,0), (5,3), (1,2), (5,1), (1,1), (5,2), (1,3)
]
def ld_49 : Array (Nat × Nat) := #[
  (0,0), (6,3), (9,2), (6,1), (9,1), (40,2), (9,3), (0,0), (34,3), (9,2),
  (40,1), (9,1), (34,2), (1,3), (0,0), (13,3), (8,2), (40,1), (9,1), (20,2),
  (9,3), (0,0), (40,3), (9,2), (34,1), (9,1), (6,2), (8,3), (0,0), (20,3),
  (9,2), (27,1), (8,1), (40,2), (9,3), (0,0), (40,3), (9,2), (20,1), (1,1),
  (27,2), (9,3), (0,0), (27,3), (1,2), (13,1), (9,1), (13,2), (9,3)
]
def ld_11 : Array (Nat × Nat) := #[
  (0,0), (3,2), (3,1), (4,1), (7,1), (7,3), (4,3), (4,1), (7,1), (5,1),
  (5,2)
]
def ld_13 : Array (Nat × Nat) := #[
  (0,0), (2,1), (2,3), (2,2), (8,2), (3,1), (2,1), (8,1), (8,1), (3,2),
  (8,2), (8,3), (3,1)
]

theorem hld_5 : checkLargeDTable 5 5 ld_5 = true := by decide
theorem hld_25 : checkLargeDTable 5 25 ld_25 = true := by decide
theorem hld_7 : checkLargeDTable 7 7 ld_7 = true := by decide
theorem hld_49 : checkLargeDTable 7 49 ld_49 = true := by decide
theorem hld_11 : checkLargeDTable 11 11 ld_11 = true := by decide
theorem hld_13 : checkLargeDTable 13 13 ld_13 = true := by decide

/-- Explicit collision table for all 245 remaining smooth moduli m = 2^a * 5^c * 7^d * 11^e * 13^f. -/
def smoothTable : List (Nat × Nat × Nat) := [
  (5,1,2), (7,1,5), (10,2,6), (11,3,5), (13,2,3), (14,1,5),
  (20,2,6), (22,3,5), (25,3,4), (26,2,8), (28,1,5), (35,2,6),
  (40,1,17), (44,7,11), (49,1,8), (50,4,8), (52,3,15), (55,7,11),
  (56,5,29), (65,3,8), (70,2,6), (77,4,11), (80,1,17), (88,7,15),
  (91,8,15), (98,9,13), (100,4,8), (104,8,16), (110,7,11), (112,1,33),
  (130,2,16), (140,2,6), (143,3,16), (154,4,18), (160,2,66), (175,4,18),
  (176,7,55), (182,2,16), (196,9,13), (200,4,28), (208,2,34), (220,7,11),
  (224,1,33), (245,9,13), (260,8,28), (275,4,18), (280,12,36), (286,8,28),
  (308,22,26), (320,2,66), (325,3,8), (350,4,18), (352,5,69), (364,2,34),
  (385,1,12), (392,8,40), (400,13,29), (416,2,34), (440,14,38), (448,5,197),
  (455,2,16), (490,9,13), (520,2,42), (539,9,20), (550,4,18), (560,5,85),
  (572,8,28), (616,6,30), (637,8,15), (650,8,28), (700,29,33), (704,5,69),
  (715,8,28), (728,2,34), (770,4,18), (784,8,40), (800,4,68), (832,3,67),
  (880,19,83), (910,2,16), (980,9,13), (1001,11,18), (1040,24,88), (1078,15,29),
  (1100,8,28), (1120,2,226), (1144,15,55), (1225,8,29), (1232,26,106), (1274,15,29),
  (1300,8,28), (1400,47,71), (1430,8,28), (1456,2,34), (1540,22,26), (1568,8,40),
  (1600,4,68), (1760,19,83), (1820,8,68), (1925,4,18), (1960,1,57), (2002,15,29),
  (2080,24,88), (2156,1,89), (2200,22,62), (2240,1,257), (2275,8,29), (2288,16,80),
  (2450,29,43), (2464,7,231), (2548,6,58), (2600,2,42), (2695,15,40), (2800,12,92),
  (2860,8,28), (2912,2,34), (3080,47,71), (3136,13,205), (3185,8,29), (3520,19,83),
  (3575,8,28), (3640,2,146), (3850,4,18), (3920,27,107), (4004,40,92), (4160,24,88),
  (4312,1,89), (4400,37,117), (4550,8,54), (4576,16,80), (4900,48,104), (4928,15,271),
  (5005,37,62), (5096,57,89), (5200,29,93), (5390,22,92), (5600,4,228), (5720,15,55),
  (5824,2,450), (6160,26,106), (6370,62,76), (7007,15,29), (7150,8,28), (7280,2,146),
  (7700,29,33), (7840,22,246), (8008,36,148), (8624,6,118), (8800,82,146), (9100,8,68),
  (9152,16,80), (9800,48,104), (10010,18,88), (10192,57,89), (10400,29,93), (10780,22,106),
  (11200,23,279), (11440,18,114), (12320,7,231), (12740,57,141), (13475,15,40), (14014,15,29),
  (14300,8,28), (14560,6,422), (15400,47,71), (15680,58,314), (15925,8,29), (16016,36,148),
  (17248,22,246), (17600,82,146), (18200,2,146), (19600,27,107), (20020,44,128), (20384,57,89),
  (20800,29,93), (21560,125,205), (22880,18,114), (24640,191,447), (25025,37,62), (25480,8,288),
  (26950,22,92), (28028,40,92), (28600,88,128), (29120,3,899), (30800,48,128), (31850,57,127),
  (32032,5,421), (34496,29,477), (35035,29,99), (36400,2,146), (39200,22,246), (40040,135,335),
  (40768,15,463), (43120,125,205), (45760,107,171), (50050,18,88), (50960,187,491), (53900,62,202),
  (56056,36,148), (57200,107,171), (61600,22,246), (63700,127,187), (64064,18,466), (70070,29,99),
  (72800,13,429), (78400,323,579), (80080,41,457), (86240,22,246), (100100,187,271), (101920,83,499),
  (107800,36,236), (112112,36,148), (114400,107,171), (123200,246,502), (127400,8,288), (140140,132,216),
  (145600,133,1029), (160160,41,457), (172480,323,579), (175175,8,138), (200200,135,335), (203840,76,972),
  (215600,22,246), (224224,106,554), (228800,107,171), (254800,138,554), (280280,187,491), (320320,94,1438),
  (350350,8,138), (400400,96,512), (431200,22,246), (448448,106,554), (509600,138,554), (560560,187,491),
  (700700,283,479), (800800,96,512), (862400,323,579), (1019200,146,1042), (1121120,181,597), (1401400,146,762),
  (1601600,62,2046), (2242240,237,1581), (2802800,1038,1518), (5605600,1038,1518), (11211200,1804,3788)
]

def pow2Floor (m : Nat) : Nat :=
  let rec go (p fuel : Nat) : Nat :=
    match fuel with
    | 0 => p
    | fuel' + 1 => if 2 * p ≤ m then go (2 * p) fuel' else p
  go 1 (Nat.log2 m + 1)

def checkSmoothAll : Bool :=
  smoothTable.all fun (m, x, y) =>
    1 ≤ x && x < y && y ≤ pow2Floor m + 1 &&
    (2 * x * x * x + x) % m == (2 * y * y * y + y) % m

def allSmoothCovered : Bool :=
  (List.range 7).all fun a =>
  (List.range 3).all fun c =>
  (List.range 3).all fun d =>
  (List.range 2).all fun e =>
  (List.range 2).all fun g =>
    if c == 0 && d == 0 && e == 0 && g == 0 then true
    else
      let m := 2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ g
      smoothTable.any fun (m', _, _) => m' == m

set_option maxRecDepth 4000 in
theorem hSmoothCheck : checkSmoothAll = true := by decide
set_option maxRecDepth 4000 in
theorem hSmoothCover : allSmoothCovered = true := by decide


/-- From ConicBox p e and m = p^e * d (p ≥ 5 prime, e ≥ 1, ¬ p ∣ d, d > 0), get collision y ≤ m / 2. -/
theorem collision_of_conicBox {m p e d : Nat} (hm : m = p ^ e * d)
    (hp : IsPrime p) (hp5 : 5 ≤ p) (he : 1 ≤ e) (hnd : ¬ p ∣ d) (hd : 0 < d)
    (hcb : ConicBox p e) :
    ∃ x y, 1 ≤ x ∧ x < y ∧ y ≤ m / 2 ∧ f x % m = f y % m := by
  have hp_pos : 0 < p := by omega
  have hpe_pos : 0 < p ^ e := Nat.pow_pos hp_pos
  have hpe_ge5 : 5 ≤ p ^ e := by
    cases e with
    | zero => omega
    | succ k =>
      have : 1 ≤ p ^ k := Nat.pow_pos hp_pos
      have : p * 1 ≤ p * p ^ k := Nat.mul_le_mul_left p this
      rw [Nat.pow_succ, Nat.mul_comm]; omega
  have hnd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hcop2 : Nat.gcd 2 p = 1 := by rw [Nat.gcd_comm]; exact coprime_of_prime_not_dvd hp hnd2
  have hcopd : Nat.gcd d p = 1 := by rw [Nat.gcd_comm]; exact coprime_of_prime_not_dvd hp hnd
  have hcop_2d2_p : Nat.gcd (2 * d ^ 2) p = 1 := by
    rw [Nat.pow_two]; exact coprime_mul_left hcop2 (coprime_mul_left hcopd hcopd)
  have hcop_2d2 : Nat.gcd (2 * d ^ 2) (p ^ e) = 1 := coprime_pow_right e hcop_2d2_p
  obtain ⟨inv, hinv_lt, hinv⟩ := exists_mod_inv hpe_pos hcop_2d2
  rw [Nat.mod_eq_of_lt (by omega : 1 < p ^ e)] at hinv
  have hinv_pos : 0 < inv := by
    cases inv with | zero => simp at hinv | succ _ => omega
  let c := p ^ e - inv
  have hndc : ¬ p ∣ c := by
    intro hpc
    have hpe_dvd : p ∣ p ^ e := by
      cases e with | zero => omega | succ k => exact ⟨p ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    have hpinv : p ∣ inv := by
      obtain ⟨a, ha⟩ := hpe_dvd
      obtain ⟨b, hb⟩ := hpc
      exact ⟨a - b, by rw [Nat.mul_sub, ← ha, ← hb]; omega⟩
    have h1 : p ∣ 2 * d ^ 2 * inv := by
      obtain ⟨k, hk⟩ := hpinv
      exact ⟨2 * d ^ 2 * k, by rw [hk]; grind⟩
    have hmodp : (2 * d ^ 2 * inv) % p = 1 := by
      have hdiv := Nat.div_add_mod (2 * d ^ 2 * inv) (p ^ e)
      rw [hinv] at hdiv
      obtain ⟨a, ha⟩ := hpe_dvd
      have hrewrite : 2 * d ^ 2 * inv = p * (a * (2 * d ^ 2 * inv / p ^ e)) + 1 := by
        calc 2 * d ^ 2 * inv = p ^ e * (2 * d ^ 2 * inv / p ^ e) + 1 := hdiv.symm
          _ = p * (a * (2 * d ^ 2 * inv / p ^ e)) + 1 := by rw [ha, Nat.mul_assoc]
      rw [hrewrite, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : 1 < p)]
    have := Nat.mod_eq_zero_of_dvd h1
    omega
  obtain ⟨u, v, hu1, huv, hv_le, hconic, _, _⟩ := hcb c hndc
  let x := u * d
  let y := v * d
  have hxy : x < y := Nat.mul_lt_mul_of_pos_right huv hd
  have hy_le : y ≤ m / 2 := by
    have h1 : 2 * v ≤ p ^ e - 1 := by omega
    have h2 : 2 * (v * d) ≤ (p ^ e - 1) * d := by
      have : 2 * (v * d) = (2 * v) * d := by grind
      rw [this]; exact Nat.mul_le_mul_right d h1
    have h3 : (p ^ e - 1) * d ≤ m := by rw [hm]; exact Nat.mul_le_mul_right d (by omega)
    omega
  have hdvdd : d ∣ f y - f x := by
    rw [f_diff_eq (Nat.le_of_lt hxy)]
    have hyx : y - x = (v - u) * d := by dsimp only [x, y]; rw [← Nat.sub_mul]
    rw [hyx]
    exact ⟨(v - u) * (2 * (x ^ 2 + x * y + y ^ 2) + 1), by grind⟩
  have hdvdpe : p ^ e ∣ f y - f x := by
    rw [f_diff_eq (Nat.le_of_lt hxy)]
    suffices hfac : p ^ e ∣ 2 * (x ^ 2 + x * y + y ^ 2) + 1 by
      obtain ⟨k, hk⟩ := hfac
      exact ⟨(y - x) * k, by rw [hk]; grind⟩
    have h1 : 2 * (x ^ 2 + x * y + y ^ 2) + 1 = (2 * d ^ 2) * (u ^ 2 + u * v + v ^ 2) + 1 := by
      dsimp only [x, y]; grind
    rw [h1]
    have hmod0 : ((2 * d ^ 2) * (u ^ 2 + u * v + v ^ 2) + 1) % p ^ e = 0 := by
      rw [Nat.add_mod, Nat.mul_mod (2 * d ^ 2), hconic, ← Nat.mul_mod (2 * d ^ 2), ← Nat.add_mod]
      have hZ : (((2 * d ^ 2 * c + 1 : Nat) : Int)) % (p ^ e : Int) = 0 := by
        have hcZ : (c : Int) = (p ^ e : Int) - (inv : Int) := Int.ofNat_sub (by omega)
        have hinvZ : ((2 * d ^ 2 * inv : Nat) : Int) % (p ^ e : Int) = 1 := by exact_mod_cast hinv
        have hsub0 : (((2 * d ^ 2 * inv : Nat) : Int) - 1) % (p ^ e : Int) = 0 := by
          rw [Int.sub_emod, hinvZ, Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 1) (by omega : (1 : Int) < (p ^ e : Int))]; simp
        obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hsub0
        have hEqZ : ((2 * d ^ 2 * c + 1 : Nat) : Int) = (p ^ e : Int) * ((2 * d ^ 2 : Int) - q) := by
          push_cast; rw [hcZ]; push_cast at hq; grind
        rw [hEqZ, Int.mul_emod_right]
      exact_mod_cast hZ
    exact Nat.dvd_of_mod_eq_zero hmod0
  have hcop_ped : Nat.gcd (p ^ e) d = 1 := coprime_pow_left e (coprime_of_prime_not_dvd hp hnd)
  have hdvdm : m ∣ f y - f x := by rw [hm]; exact dvd_mul_of_coprime hcop_ped hdvdpe hdvdd
  exact ⟨x, y, by have : 1 * 1 ≤ u * d := Nat.mul_le_mul hu1 hd; omega, hxy, hy_le,
         (mod_eq_iff_dvd_sub (f_mono (Nat.le_of_lt hxy))).mpr hdvdm⟩

/-- From a verified LargeD table for (p, q = p^e), get collision y ≤ m / 2 + 1 whenever d ≥ 2*q - 2. -/
theorem collision_of_largeD {m p e d : Nat} (hm : m = p ^ e * d)
    (hp : IsPrime p) (he : 1 ≤ e) (hnd : ¬ p ∣ d) (hd : 2 * p ^ e - 2 ≤ d)
    (tab : Array (Nat × Nat)) (hcheck : checkLargeDTable p (p ^ e) tab = true) :
    ∃ x y, 1 ≤ x ∧ x < y ∧ y ≤ m / 2 + 1 ∧ f x % m = f y % m := by
  have hp_pos : 0 < p := by have := hp.1; omega
  have hq_pos : 0 < p ^ e := Nat.pow_pos hp_pos
  have hd_pos : 0 < d := by
    have : 2 ≤ p ^ e := by
      cases e with
      | zero => omega
      | succ k =>
        have : 1 ≤ p ^ k := Nat.pow_pos hp_pos
        have := Nat.mul_le_mul_left p this
        have := hp.1
        rw [Nat.pow_succ, Nat.mul_comm]; omega
    omega
  have hd0_lt : d % p ^ e < p ^ e := Nat.mod_lt d hq_pos
  unfold checkLargeDTable at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hcheck
  have hrow := hcheck.2 (d % p ^ e) hd0_lt
  have hnd_mod : (d % p ^ e) % p ≠ 0 := by
    intro h0
    apply hnd
    have hpe_dvd : p ∣ p ^ e := by
      cases e with | zero => omega | succ k => exact ⟨p ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    obtain ⟨a, ha⟩ := hpe_dvd
    have hdiv := Nat.div_add_mod d (p ^ e)
    obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero h0
    refine ⟨a * (d / p ^ e) + b, ?_⟩
    have : p ^ e * (d / p ^ e) = p * (a * (d / p ^ e)) := by rw [ha, Nat.mul_assoc]
    rw [Nat.mul_add, ← this, ← hb]; omega
  rw [ite_eq_right (by simp [hnd_mod])] at hrow
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hrow
  let xt := tab[d % p ^ e]!
  let x := xt.1
  let t := xt.2
  have hx1 : 1 ≤ x := hrow.1.1.1.1
  have hx_le : x ≤ p ^ e := hrow.1.1.1.2
  have ht1 : 1 ≤ t := hrow.1.1.2
  have ht_le : t ≤ (p ^ e - 1) / 2 := hrow.1.2
  have hmod0 : (2 * (x * x + x * (x + t * (d % p ^ e)) + (x + t * (d % p ^ e)) * (x + t * (d % p ^ e))) + 1) % p ^ e = 0 := hrow.2
  let y := x + t * d
  have hxy : x < y := by
    have : 1 * 1 ≤ t * d := Nat.mul_le_mul ht1 hd_pos
    omega
  have hy_le : y ≤ m / 2 + 1 := by
    have h2t : 2 * t ≤ p ^ e - 1 := by omega
    have hmul : (2 * t) * d ≤ (p ^ e - 1) * d := Nat.mul_le_mul_right d h2t
    have hpe_d : (p ^ e - 1) * d + d = m := by
      rw [hm]; cases hpe : p ^ e with
      | zero => omega
      | succ k => simp [Nat.succ_mul]
    have h2y : 2 * y ≤ m + 2 := by
      have : 2 * y = 2 * x + (2 * t) * d := by dsimp only [y]; grind
      omega
    omega
  have hdvdd : d ∣ f y - f x := by
    rw [f_diff_eq (Nat.le_of_lt hxy)]
    have hyx : y - x = t * d := by dsimp only [y]; omega
    rw [hyx]
    exact ⟨t * (2 * (x ^ 2 + x * y + y ^ 2) + 1), by grind⟩
  have hdvdpe : p ^ e ∣ f y - f x := by
    rw [f_diff_eq (Nat.le_of_lt hxy)]
    suffices hfac : p ^ e ∣ 2 * (x ^ 2 + x * y + y ^ 2) + 1 by
      obtain ⟨k, hk⟩ := hfac
      exact ⟨(y - x) * k, by rw [hk]; grind⟩
    -- Since d ≡ d % p^e (mod p^e), y = x + t*d ≡ x + t*(d % p^e) (mod p^e)
    have hcong : (2 * (x ^ 2 + x * y + y ^ 2) + 1) % p ^ e =
                 (2 * (x * x + x * (x + t * (d % p ^ e)) + (x + t * (d % p ^ e)) * (x + t * (d % p ^ e))) + 1) % p ^ e := by
      have hdiv := Nat.div_add_mod d (p ^ e)
      have hy_eq : y = (x + t * (d % p ^ e)) + p ^ e * (t * (d / p ^ e)) := by
        dsimp only [y]; grind
      let y0 := x + t * (d % p ^ e)
      let k := t * (d / p ^ e)
      have hZ : ((2 * (x ^ 2 + x * y + y ^ 2) + 1 : Nat) : Int) =
                ((2 * (x * x + x * y0 + y0 * y0) + 1 : Nat) : Int) +
                (p ^ e : Int) * (2 * (k : Int) * ((x : Int) + 2 * (y0 : Int) + (p ^ e : Int) * (k : Int))) := by
        have hyZ : (y : Int) = (y0 : Int) + (p ^ e : Int) * (k : Int) := by exact_mod_cast hy_eq
        push_cast; rw [hyZ]; grind
      have hmodZ : ((2 * (x ^ 2 + x * y + y ^ 2) + 1 : Nat) : Int) % (p ^ e : Int) =
                   ((2 * (x * x + x * y0 + y0 * y0) + 1 : Nat) : Int) % (p ^ e : Int) := by
        rw [hZ, Int.add_mul_emod_self_left]
      exact_mod_cast hmodZ
    exact Nat.dvd_of_mod_eq_zero (by rw [hcong]; exact hmod0)
  have hcop : Nat.gcd (p ^ e) d = 1 := coprime_pow_left e (coprime_of_prime_not_dvd hp hnd)
  have hdvdm : m ∣ f y - f x := by rw [hm]; exact dvd_mul_of_coprime hcop hdvdpe hdvdd
  exact ⟨x, y, hx1, hxy, hy_le, (mod_eq_iff_dvd_sub (f_mono (Nat.le_of_lt hxy))).mpr hdvdm⟩

/-! ### Section 7: Factorization, Smooth Case, and Main Theorem -/

theorem pow2Floor_le (m : Nat) (hm : 1 ≤ m) :
    pow2Floor m ≤ m ∧ m < 2 * pow2Floor m := by
  -- Prove invariant of pow2Floor.go
  have hgo : ∀ (fuel p : Nat), 1 ≤ p → p ≤ m → m < p * 2 ^ fuel →
      pow2Floor.go m p fuel ≤ m ∧ m < 2 * pow2Floor.go m p fuel := by
    intro fuel
    induction fuel with
    | zero =>
      intro p hp hpm hlt
      simp only [pow2Floor.go, Nat.pow_zero, Nat.mul_one] at *
      omega
    | succ f' ih =>
      intro p hp hpm hlt
      simp only [pow2Floor.go]
      split
      · rename_i h2p
        apply ih (2 * p) (by omega) h2p
        have : 2 * p * 2 ^ f' = p * 2 ^ (f' + 1) := by rw [Nat.pow_succ]; grind
        omega
      · rename_i h2p
        omega
  have hlt : m < 1 * 2 ^ (Nat.log2 m + 1) := by
    rw [Nat.one_mul]
    have hlog := Nat.lt_log2_self (n := m)
    -- Use Nat.log2_lt directly:
    by_cases hm0 : m = 0
    · omega
    · exact (Nat.log2_lt hm0).mp (Nat.lt_succ_self (Nat.log2 m))
  exact hgo (Nat.log2 m + 1) 1 (by omega) hm hlt

theorem pow2Floor_is_pow2 (m : Nat) : ∃ r, pow2Floor m = 2 ^ r := by
  have hgo : ∀ (fuel k : Nat), ∃ r, pow2Floor.go m (2 ^ k) fuel = 2 ^ r := by
    intro fuel
    induction fuel with
    | zero => intro k; exact ⟨k, rfl⟩
    | succ f' ih =>
      intro k
      simp only [pow2Floor.go]
      split
      · have h2 : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [h2]; exact ih (k + 1)
      · exact ⟨k, rfl⟩
  exact hgo (Nat.log2 m + 1) 0

theorem factor_out_prime (p : Nat) (hp : 2 ≤ p) :
    ∀ n, 0 < n → ∃ e d, n = p ^ e * d ∧ ¬ (p ∣ d) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h : p ∣ n
    · obtain ⟨q, hq⟩ := h
      have hq_pos : 0 < q := by
        cases q with | zero => simp at hq; omega | succ _ => omega
      have hq_lt : q < n := by
        have : 2 * q ≤ p * q := Nat.mul_le_mul_right q hp
        omega
      obtain ⟨e, d, hed, hnd⟩ := ih q hq_lt hq_pos
      exact ⟨e + 1, d, by rw [hq, hed, Nat.pow_succ]; grind, hnd⟩
    · exact ⟨0, n, by simp, h⟩

theorem exists_prime_factor : ∀ n, 2 ≤ n → ∃ p, IsPrime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hpr : IsPrime n
    · exact ⟨n, hpr, Nat.dvd_refl n⟩
    · -- Not prime, so has a divisor d with 2 ≤ d < n
      have hex : ∃ d, d ∣ n ∧ 2 ≤ d ∧ d < n := by
        apply Classical.byContradiction
        intro hno
        apply hpr
        refine ⟨hn, fun d hd => ?_⟩
        have hle := Nat.le_of_dvd (by omega) hd
        have hne0 : d ≠ 0 := fun h0 => by rw [h0] at hd; obtain ⟨k, hk⟩ := hd; omega
        by_cases h1 : d = 1
        · exact Or.inl h1
        · by_cases hn' : d = n
          · exact Or.inr hn'
          · exfalso; exact hno ⟨d, hd, by omega, by omega⟩
      obtain ⟨d, hdn, hd2, hdlt⟩ := hex
      obtain ⟨p, hp, hpd⟩ := ih d hdlt hd2
      exact ⟨p, hp, Nat.dvd_trans hpd hdn⟩

theorem isPrime_5 : IsPrime 5 := ⟨by omega, fun d hd => by
  have := Nat.le_of_dvd (by omega) hd
  have : d ≠ 0 := fun h0 => by rw [h0] at hd; exact absurd hd (by decide)
  have : d ≠ 2 := fun h => by rw [h] at hd; exact absurd hd (by decide)
  have : d ≠ 3 := fun h => by rw [h] at hd; exact absurd hd (by decide)
  have : d ≠ 4 := fun h => by rw [h] at hd; exact absurd hd (by decide)
  omega⟩

theorem isPrime_7 : IsPrime 7 := ⟨by omega, fun d hd => by
  have := Nat.le_of_dvd (by omega) hd
  have : d ≠ 0 := fun h0 => by rw [h0] at hd; exact absurd hd (by decide)
  have : d ≠ 2 := fun h => by rw [h] at hd; exact absurd hd (by decide)
  have : d ≠ 3 := fun h => by rw [h] at hd; exact absurd hd (by decide)
  have : d ≠ 4 := fun h => by rw [h] at hd; exact absurd hd (by decide)
  have : d ≠ 5 := fun h => by rw [h] at hd; exact absurd hd (by decide)
  have : d ≠ 6 := fun h => by rw [h] at hd; exact absurd hd (by decide)
  omega⟩

theorem isPrime_11 : IsPrime 11 := ⟨by omega, fun d hd => by
  have hle := Nat.le_of_dvd (by omega) hd
  have hne : ∀ k, k < 11 → k ≠ 1 → ¬ k ∣ 11 := by decide
  by_cases h1 : d = 1
  · exact Or.inl h1
  · by_cases h11 : d = 11
    · exact Or.inr h11
    · exact absurd hd (hne d (by omega) h1)⟩

theorem isPrime_13 : IsPrime 13 := ⟨by omega, fun d hd => by
  have hle := Nat.le_of_dvd (by omega) hd
  have hne : ∀ k, k < 13 → k ≠ 1 → ¬ k ∣ 13 := by decide
  by_cases h1 : d = 1
  · exact Or.inl h1
  · by_cases h13 : d = 13
    · exact Or.inr h13
    · exact absurd hd (hne d (by omega) h1)⟩

/-- Core lower bound: every positive integer m that is not a power of 2 has a collision ≤ pow2Floor m + 1. -/
theorem collision_of_not_pow2 {m : Nat} (hm : 1 ≤ m) (hnot : ∀ r, m ≠ 2 ^ r) :
    ∃ x y, 1 ≤ x ∧ x < y ∧ y ≤ pow2Floor m + 1 ∧ f x % m = f y % m := by
  have hpf := pow2Floor_le m hm
  -- Note: m / 2 + 1 ≤ pow2Floor m + 1 since m < 2 * pow2Floor m!
  have hhalf_le : m / 2 + 1 ≤ pow2Floor m + 1 := by omega
  -- Case 1: 3 ∣ m
  by_cases h3 : 3 ∣ m
  · obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_three_dvd h3 (by omega)
    exact ⟨x, y, hx1, hxy, by omega, hmod⟩
  -- Factor out 2, 5, 7, 11, 13 from m:
  obtain ⟨a, m1, hm1, hnd2⟩ := factor_out_prime 2 (by omega) m (by omega)
  have hm1_pos : 0 < m1 := by cases m1 with | zero => simp at hm1; omega | succ _ => omega
  obtain ⟨c, m2, hm2, hnd5⟩ := factor_out_prime 5 (by omega) m1 hm1_pos
  have hm2_pos : 0 < m2 := by cases m2 with | zero => simp at hm2; omega | succ _ => omega
  obtain ⟨d, m3, hm3, hnd7⟩ := factor_out_prime 7 (by omega) m2 hm2_pos
  have hm3_pos : 0 < m3 := by cases m3 with | zero => simp at hm3; omega | succ _ => omega
  obtain ⟨e, m4, hm4, hnd11⟩ := factor_out_prime 11 (by omega) m3 hm3_pos
  have hm4_pos : 0 < m4 := by cases m4 with | zero => simp at hm4; omega | succ _ => omega
  obtain ⟨g, rem, hrem, hnd13⟩ := factor_out_prime 13 (by omega) m4 hm4_pos
  have hrem_pos : 0 < rem := by cases rem with | zero => simp at hrem; omega | succ _ => omega
  have hm_full : m = 2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ g * rem := by
    rw [hm1, hm2, hm3, hm4, hrem]; grind
  -- Case 2: rem ≥ 2, so rem has a prime factor p ≥ 17!
  by_cases hrem2 : 2 ≤ rem
  · obtain ⟨p, hp, hprem⟩ := exists_prime_factor rem hrem2
    have hp_ge17 : 17 ≤ p := by
      have hp_dvd_m : p ∣ m := by rw [hm_full]; obtain ⟨k, hk⟩ := hprem; exact ⟨2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ g * k, by rw [hk]; grind⟩
      have hne2 : p ≠ 2 := fun h => by rw [h] at hprem; exact hnd2 (by rw [hm2, hm3, hm4, hrem]; obtain ⟨k, hk⟩ := hprem; exact ⟨5^c*7^d*11^e*13^g*k, by rw [hk]; grind⟩)
      have hne3 : p ≠ 3 := fun h => by rw [h] at hp_dvd_m; exact h3 hp_dvd_m
      have hne5 : p ≠ 5 := fun h => by rw [h] at hprem; exact hnd5 (by rw [hm3, hm4, hrem]; obtain ⟨k, hk⟩ := hprem; exact ⟨7^d*11^e*13^g*k, by rw [hk]; grind⟩)
      have hne7 : p ≠ 7 := fun h => by rw [h] at hprem; exact hnd7 (by rw [hm4, hrem]; obtain ⟨k, hk⟩ := hprem; exact ⟨11^e*13^g*k, by rw [hk]; grind⟩)
      have hne11 : p ≠ 11 := fun h => by rw [h] at hprem; exact hnd11 (by rw [hrem]; obtain ⟨k, hk⟩ := hprem; exact ⟨13^g*k, by rw [hk]; grind⟩)
      have hne13 : p ≠ 13 := fun h => by rw [h] at hprem; exact hnd13 hprem
      have hcomp : ∀ k, 2 ≤ k → k < 17 → k ≠ 2 → k ≠ 3 → k ≠ 5 → k ≠ 7 → k ≠ 11 → k ≠ 13 → ¬ IsPrime k := by
        intro k hk2 hk17 h2 h3' h5 h7 h11 h13 hpk
        have : k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 12 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rcases hpk.2 2 (by decide) with h | h <;> omega
        · rcases hpk.2 2 (by decide) with h | h <;> omega
        · rcases hpk.2 2 (by decide) with h | h <;> omega
        · rcases hpk.2 3 (by decide) with h | h <;> omega
        · rcases hpk.2 2 (by decide) with h | h <;> omega
        · rcases hpk.2 2 (by decide) with h | h <;> omega
        · rcases hpk.2 2 (by decide) with h | h <;> omega
        · rcases hpk.2 3 (by decide) with h | h <;> omega
        · rcases hpk.2 2 (by decide) with h | h <;> omega
      by_cases hlt17 : p < 17
      · exact absurd hp (hcomp p hp.1 hlt17 hne2 hne3 hne5 hne7 hne11 hne13)
      · omega
    obtain ⟨k, cof, hmcof, hndp⟩ := factor_out_prime p hp.1 m (by omega)
    have hk1 : 1 ≤ k := by
      cases k with
      | zero =>
        simp at hmcof
        have hp_dvd_m : p ∣ m := by rw [hm_full]; obtain ⟨q, hq⟩ := hprem; exact ⟨2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ g * q, by rw [hq]; grind⟩
        rw [hmcof] at hp_dvd_m; exact absurd hp_dvd_m hndp
      | succ _ => omega
    have hcof_pos : 0 < cof := by cases cof with | zero => simp at hmcof; omega | succ _ => omega
    have hcb : ConicBox p k := conicBox_of_base hp (by omega) (by omega) (conicBox_prime hp hp_ge17) k hk1
    obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_conicBox hmcof hp (by omega) hk1 hndp hcof_pos hcb
    exact ⟨x, y, hx1, hxy, by omega, hmod⟩
  -- Now rem = 1!
  have hrem1 : rem = 1 := by omega
  rw [hrem1, Nat.mul_one] at hm_full
  -- Helper: ¬ p ∣ product of other primes
  have hnd_of_prod : ∀ {p q1 q2 q3 q4 : Nat}, IsPrime p → ¬ p ∣ q1 → ¬ p ∣ q2 → ¬ p ∣ q3 → ¬ p ∣ q4 →
      ∀ {e1 e2 e3 e4 : Nat}, ¬ p ∣ (q1 ^ e1 * q2 ^ e2 * q3 ^ e3 * q4 ^ e4) := by
    intro p q1 q2 q3 q4 hp h1 h2 h3' h4 e1 e2 e3 e4
    have hpow : ∀ {q : Nat}, ¬ p ∣ q → ∀ k, ¬ p ∣ q ^ k := by
      intro q hq k
      induction k with
      | zero => simp; intro h; have := hp.1; omega
      | succ j ih =>
        rw [Nat.pow_succ]; intro h
        rcases prime_dvd_mul hp h with h1' | h2'
        · exact ih h1'
        · exact hq h2'
    intro h
    rcases prime_dvd_mul hp h with h123 | h4'
    · rcases prime_dvd_mul hp h123 with h12 | h3''
      · rcases prime_dvd_mul hp h12 with h1' | h2'
        · exact hpow h1 e1 h1'
        · exact hpow h2 e2 h2'
      · exact hpow h3' e3 h3''
    · exact hpow h4 e4 h4'
  -- Case 3a: c ≥ 3 (5^3 ∣ m)
  by_cases hc3 : 3 ≤ c
  · let cof := 2 ^ a * 7 ^ d * 11 ^ e * 13 ^ g
    have hmcof : m = 5 ^ c * cof := by rw [hm_full]; dsimp only [cof]; grind
    have hnd : ¬ 5 ∣ cof := hnd_of_prod isPrime_5 (by decide) (by decide) (by decide) (by decide)
    have hcof_pos : 0 < cof := by
      dsimp only [cof]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
    obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_conicBox hmcof isPrime_5 (by omega) (by omega) hnd hcof_pos
      (conicBox_of_base isPrime_5 (by omega) (by omega) base_5_3 c hc3)
    exact ⟨x, y, hx1, hxy, by omega, hmod⟩
  -- Case 3b: d ≥ 3 (7^3 ∣ m)
  by_cases hd3 : 3 ≤ d
  · let cof := 2 ^ a * 5 ^ c * 11 ^ e * 13 ^ g
    have hmcof : m = 7 ^ d * cof := by rw [hm_full]; dsimp only [cof]; grind
    have hnd : ¬ 7 ∣ cof := hnd_of_prod isPrime_7 (by decide) (by decide) (by decide) (by decide)
    have hcof_pos : 0 < cof := by
      dsimp only [cof]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
    obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_conicBox hmcof isPrime_7 (by omega) (by omega) hnd hcof_pos
      (conicBox_of_base isPrime_7 (by omega) (by omega) base_7_3 d hd3)
    exact ⟨x, y, hx1, hxy, by omega, hmod⟩
  -- Case 3c: e ≥ 2 (11^2 ∣ m)
  by_cases he2 : 2 ≤ e
  · let cof := 2 ^ a * 5 ^ c * 7 ^ d * 13 ^ g
    have hmcof : m = 11 ^ e * cof := by rw [hm_full]; dsimp only [cof]; grind
    have hnd : ¬ 11 ∣ cof := hnd_of_prod isPrime_11 (by decide) (by decide) (by decide) (by decide)
    have hcof_pos : 0 < cof := by
      dsimp only [cof]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
    obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_conicBox hmcof isPrime_11 (by omega) (by omega) hnd hcof_pos
      (conicBox_of_base isPrime_11 (by omega) (by omega) base_11_2 e he2)
    exact ⟨x, y, hx1, hxy, by omega, hmod⟩
  -- Case 3d: g ≥ 2 (13^2 ∣ m)
  by_cases hg2 : 2 ≤ g
  · let cof := 2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e
    have hmcof : m = 13 ^ g * cof := by rw [hm_full]; dsimp only [cof]; grind
    have hnd : ¬ 13 ∣ cof := hnd_of_prod isPrime_13 (by decide) (by decide) (by decide) (by decide)
    have hcof_pos : 0 < cof := by
      dsimp only [cof]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
    obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_conicBox hmcof isPrime_13 (by omega) (by omega) hnd hcof_pos
      (conicBox_of_base isPrime_13 (by omega) (by omega) base_13_2 g hg2)
    exact ⟨x, y, hx1, hxy, by omega, hmod⟩
  -- Case 4: c ≤ 2, d ≤ 2, e ≤ 1, g ≤ 1, and at least one of c, d, e, g is nonzero (since m ≠ 2^a)!
  have hnot_all0 : ¬ (c = 0 ∧ d = 0 ∧ e = 0 ∧ g = 0) := by
    intro ⟨hc0, hd0, he0, hg0⟩
    rw [hc0, hd0, he0, hg0] at hm_full
    simp at hm_full
    exact hnot a hm_full
  by_cases ha7 : 7 ≤ a
  · -- Subcase 4a: 2^a ≥ 128 ≥ 2*49 - 2!
    have h2a : 128 ≤ 2 ^ a := by
      have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha7
      omega
    by_cases hc1 : 1 ≤ c
    · let cof := 2 ^ a * 7 ^ d * 11 ^ e * 13 ^ g
      have hmcof : m = 5 ^ c * cof := by rw [hm_full]; dsimp only [cof]; grind
      have hnd : ¬ 5 ∣ cof := hnd_of_prod isPrime_5 (by decide) (by decide) (by decide) (by decide)
      have hcof_ge : 128 ≤ cof := by
        dsimp only [cof]
        have h1 : 1 ≤ 7 ^ d * 11 ^ e * 13 ^ g :=
          Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
        have := Nat.mul_le_mul h2a h1
        have : 2 ^ a * 7 ^ d * 11 ^ e * 13 ^ g = 2 ^ a * (7 ^ d * 11 ^ e * 13 ^ g) := by grind
        omega
      have hc_cases : c = 1 ∨ c = 2 := by omega
      rcases hc_cases with rfl | rfl
      · obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_largeD hmcof isPrime_5 (by omega) hnd (by omega) ld_5 hld_5
        exact ⟨x, y, hx1, hxy, by omega, hmod⟩
      · obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_largeD hmcof isPrime_5 (by omega) hnd (by omega) ld_25 hld_25
        exact ⟨x, y, hx1, hxy, by omega, hmod⟩
    · by_cases hd1 : 1 ≤ d
      · let cof := 2 ^ a * 5 ^ c * 11 ^ e * 13 ^ g
        have hmcof : m = 7 ^ d * cof := by rw [hm_full]; dsimp only [cof]; grind
        have hnd : ¬ 7 ∣ cof := hnd_of_prod isPrime_7 (by decide) (by decide) (by decide) (by decide)
        have hcof_ge : 128 ≤ cof := by
          dsimp only [cof]
          have h1 : 1 ≤ 5 ^ c * 11 ^ e * 13 ^ g :=
            Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
          have := Nat.mul_le_mul h2a h1
          have : 2 ^ a * 5 ^ c * 11 ^ e * 13 ^ g = 2 ^ a * (5 ^ c * 11 ^ e * 13 ^ g) := by grind
          omega
        have hd_cases : d = 1 ∨ d = 2 := by omega
        rcases hd_cases with rfl | rfl
        · obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_largeD hmcof isPrime_7 (by omega) hnd (by omega) ld_7 hld_7
          exact ⟨x, y, hx1, hxy, by omega, hmod⟩
        · obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_largeD hmcof isPrime_7 (by omega) hnd (by omega) ld_49 hld_49
          exact ⟨x, y, hx1, hxy, by omega, hmod⟩
      · by_cases he1 : 1 ≤ e
        · have he_eq : e = 1 := by omega
          subst he_eq
          let cof := 2 ^ a * 5 ^ c * 7 ^ d * 13 ^ g
          have hmcof : m = 11 ^ 1 * cof := by rw [hm_full]; dsimp only [cof]; grind
          have hnd : ¬ 11 ∣ cof := hnd_of_prod isPrime_11 (by decide) (by decide) (by decide) (by decide)
          have hcof_ge : 128 ≤ cof := by
            dsimp only [cof]
            have h1 : 1 ≤ 5 ^ c * 7 ^ d * 13 ^ g :=
              Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
            have := Nat.mul_le_mul h2a h1
            have : 2 ^ a * 5 ^ c * 7 ^ d * 13 ^ g = 2 ^ a * (5 ^ c * 7 ^ d * 13 ^ g) := by grind
            omega
          obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_largeD hmcof isPrime_11 (by omega) hnd (by omega) ld_11 hld_11
          exact ⟨x, y, hx1, hxy, by omega, hmod⟩
        · have hg_eq : g = 1 := by omega
          subst hg_eq
          let cof := 2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e
          have hmcof : m = 13 ^ 1 * cof := by rw [hm_full]; dsimp only [cof]; grind
          have hnd : ¬ 13 ∣ cof := hnd_of_prod isPrime_13 (by decide) (by decide) (by decide) (by decide)
          have hcof_ge : 128 ≤ cof := by
            dsimp only [cof]
            have h1 : 1 ≤ 5 ^ c * 7 ^ d * 11 ^ e :=
              Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
            have := Nat.mul_le_mul h2a h1
            have : 2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e = 2 ^ a * (5 ^ c * 7 ^ d * 11 ^ e) := by grind
            omega
          obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_largeD hmcof isPrime_13 (by omega) hnd (by omega) ld_13 hld_13
          exact ⟨x, y, hx1, hxy, by omega, hmod⟩
  · -- Subcase 4b: a ≤ 6 → one of the 245 verified smooth moduli!
    have hcov := hSmoothCover
    unfold allSmoothCovered at hcov
    simp only [List.all_eq_true, List.mem_range] at hcov
    have hrow := hcov a (by omega) c (by omega) d (by omega) e (by omega) g (by omega)
    have hcond : ((c == 0 && d == 0 && e == 0 && g == 0)) = false := by
      cases hc0 : (c == 0) <;> cases hd0 : (d == 0) <;> cases he0 : (e == 0) <;> cases hg0 : (g == 0) <;> try rfl
      exfalso; apply hnot_all0
      simp only [beq_iff_eq] at hc0 hd0 he0 hg0
      exact ⟨hc0, hd0, he0, hg0⟩
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, beq_iff_eq] at hrow
    obtain ⟨⟨m', x, y⟩, hmem, hmEq⟩ := hrow
    have hm_eq : m' = m := by dsimp only at hmEq; rw [hmEq, ← hm_full]
    have hchk := hSmoothCheck
    unfold checkSmoothAll at hchk
    simp only [List.all_eq_true] at hchk
    have hentry := hchk (m', x, y) hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hentry
    rw [hm_eq] at hentry
    refine ⟨x, y, hentry.1.1.1, hentry.1.1.2, hentry.1.2, ?_⟩
    unfold f
    have hx3 : x ^ 3 = x * x * x := by simp [Nat.pow_succ, Nat.pow_zero]
    have hy3 : y ^ 3 = y * y * y := by simp [Nat.pow_succ, Nat.pow_zero]
    rw [hx3, hy3]
    have h1 : 2 * (x * x * x) = 2 * x * x * x := by grind
    have h2 : 2 * (y * y * y) = 2 * y * y * y := by grind
    rw [h1, h2]; exact hentry.2

/-- Existence of the least power of 2 not smaller than n. -/
theorem exists_least_pow2 (n : Nat) (_hn : 1 ≤ n) :
    ∃ r : Nat, n ≤ 2 ^ r ∧ (r = 0 ∨ 2 ^ (r - 1) < n) := by
  have hgo : ∀ k, n ≤ 2 ^ k → ∃ r, n ≤ 2 ^ r ∧ (r = 0 ∨ 2 ^ (r - 1) < n) := by
    intro k
    induction k with
    | zero => intro h; exact ⟨0, h, Or.inl rfl⟩
    | succ j ih =>
      intro h
      by_cases hle : n ≤ 2 ^ j
      · exact ih hle
      · exact ⟨j + 1, h, Or.inr (by simp; omega)⟩
  have hlt : n ≤ 2 ^ n := by
    have : ∀ k, k < 2 ^ k := by
      intro k; induction k with
      | zero => omega
      | succ j ih => rw [Nat.pow_succ]; omega
    exact Nat.le_of_lt (this n)
  exact hgo n hlt

/-- **Main Theorem (Zhi-Wei Sun, OEIS A356976, Conjecture 2):**
    For every positive integer n, the least positive integer m such that
    2*k^3 + k (k = 1..n) are pairwise distinct modulo m is the least power of 2
    not smaller than n. -/
theorem a356976_conjecture_2 (n : Nat) (hn : 1 ≤ n) :
    ∃ r : Nat,
      n ≤ 2 ^ r ∧
      (r = 0 ∨ 2 ^ (r - 1) < n) ∧
      DistinctMod n (2 ^ r) ∧
      ∀ m : Nat, 1 ≤ m → m < 2 ^ r → ¬ DistinctMod n m := by
  obtain ⟨r, hnr, hr_min⟩ := exists_least_pow2 n hn
  refine ⟨r, hnr, hr_min, distinctMod_pow2 n r hnr, ?_⟩
  intro m hm1 hmr hdist
  rcases hr_min with rfl | hr_lt
  · simp at hmr; omega
  · by_cases hpow : ∃ k, m = 2 ^ k
    · -- m is a power of 2 < 2^r, so m ≤ 2^(r-1) < n; pigeonhole on 1..m+1 gives a collision!
      obtain ⟨k, rfl⟩ := hpow
      have hkr : k < r := by
        by_cases hge : r ≤ k
        · have := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) hge; omega
        · omega
      have hle : 2 ^ k ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hm_lt_n : 2 ^ k < n := by omega
      let g : Fin (2 ^ k + 1) → Fin (2 ^ k) := fun i => ⟨f (i.val + 1) % 2 ^ k, Nat.mod_lt _ (by omega)⟩
      obtain ⟨i, j, hij, hgij⟩ := pigeonhole (Nat.lt_succ_self _) g
      have hEq : f (i.val + 1) % 2 ^ k = f (j.val + 1) % 2 ^ k := congrArg Fin.val hgij
      have := hdist (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega) (by omega) hEq
      omega
    · -- m is NOT a power of 2: pow2Floor m ≤ 2^(r-1) < n, so pow2Floor m + 1 ≤ n!
      have hnot : ∀ k, m ≠ 2 ^ k := fun k hk => hpow ⟨k, hk⟩
      obtain ⟨x, y, hx1, hxy, hy_le, hmod⟩ := collision_of_not_pow2 hm1 hnot
      obtain ⟨k, hk⟩ := pow2Floor_is_pow2 m
      have hpf_le : pow2Floor m ≤ m := (pow2Floor_le m hm1).1
      have hkr : k < r := by
        by_cases hge : r ≤ k
        · have := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) hge; omega
        · omega
      have hle_prev : pow2Floor m ≤ 2 ^ (r - 1) := by
        rw [hk]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have hy_le_n : y ≤ n := by omega
      have := hdist x y hx1 (by omega) (by omega) hy_le_n hmod
      omega

end A356976Conj2

#print axioms A356976Conj2.a356976_conjecture_2
