import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# A counterexample to Erdős's nonvanishing conjecture for periodic Dirichlet series

The final theorem concerns ordinary partial sums, taken in increasing order.
All coefficients of the witness and its finite identities are present in this file.
Checked in Lean 4.34.1 with mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
In that mathlib project run `lake env lean ErdosLSeries.lean`.
-/

namespace ErdosLSeries
open Finset Filter
open scoped Topology

abbrev q : ℕ := 11025
abbrev Channel := Fin 7

def symbol3 (n : ℕ) : ℤ := if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1
def symbol5 (n : ℕ) : ℤ := if n % 5 = 0 then 0 else if n % 5 = 1 ∨ n % 5 = 4 then 1 else -1
def symbol7 (n : ℕ) : ℤ := if n % 7 = 0 then 0 else if n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4 then 1 else -1

/-- The trivial sequence and six products of real quadratic characters. -/
def char (h : Channel) (n : ℕ) : ℤ :=
  let m := n % 105
  match h.val with
  | 0 => 1
  | 1 => symbol3 m
  | 2 => symbol5 m
  | 3 => symbol3 m * symbol5 m
  | 4 => symbol7 m
  | 5 => symbol3 m * symbol7 m
  | _ => symbol5 m * symbol7 m

theorem char_mod (h : Channel) (n : ℕ) : char h (n % 105) = char h n := by
  simp [char]
theorem char_period (h : Channel) : Function.Periodic (char h) 105 := by
  intro n
  simp [char]
@[simp] theorem char_zero (n : ℕ) : char 0 n = 1 := rfl

structure Row where
  d : ℕ
  a : ℤ
  deriving DecidableEq, Repr

def Row.k (t : Row) : ℕ := q / t.d
def Row.w (t : Row) : ℤ := t.a * (t.k : ℤ)

/-- Sparse integer table. A pair represents (d, twice the coefficient). -/
def rows (h : Channel) : List Row :=
  match h.val with
  | 0 => [⟨105, 1⟩, ⟨147, -1⟩, ⟨175, -1⟩, ⟨245, 1⟩, ⟨315, -1⟩, ⟨441, 1⟩, ⟨525, -1⟩, ⟨735, -1⟩, ⟨1225, 2⟩, ⟨1575, 2⟩, ⟨3675, 2⟩, ⟨11025, -4⟩]
  | 1 => [⟨21, -1⟩, ⟨25, 2⟩, ⟨75, -2⟩, ⟨105, -1⟩, ⟨147, 2⟩, ⟨175, -3⟩, ⟨245, -1⟩, ⟨525, 3⟩, ⟨735, 4⟩, ⟨3675, 1⟩]
  | 2 => [⟨147, -1⟩, ⟨245, 1⟩, ⟨441, 1⟩, ⟨735, 1⟩, ⟨2205, -2⟩]
  | 3 => [⟨21, 1⟩, ⟨49, -2⟩, ⟨105, -1⟩, ⟨245, 1⟩, ⟨735, -1⟩]
  | 4 => [⟨21, 1⟩, ⟨35, -2⟩, ⟨63, 1⟩, ⟨105, -1⟩, ⟨175, -1⟩, ⟨225, 2⟩, ⟨315, 1⟩, ⟨525, -2⟩, ⟨1575, 1⟩]
  | 5 => [⟨105, 1⟩, ⟨175, -1⟩, ⟨525, -2⟩]
  | _ => [⟨1, -2⟩, ⟨3, 4⟩, ⟨5, 2⟩, ⟨7, 2⟩, ⟨21, -1⟩, ⟨63, 1⟩, ⟨105, 1⟩, ⟨315, 1⟩]

def dilate (b : ℕ → ℤ) (d n : ℕ) : ℤ := if d ∣ n then b (n / d) else 0

def part (b : ℕ → ℤ) (rs : List Row) (n : ℕ) : ℤ :=
  (rs.map fun t => t.a * dilate b t.d n).sum

def raw (n : ℕ) : ℤ := ∑ h : Channel, part (char h) (rows h) n

/-- The actual integer-valued coefficient sequence. -/
def witness (n : ℕ) : ℤ := raw n / 2

/-- The ordinary partial sum through n, starting at the positive integer 1. -/
noncomputable def partialL (b : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, (b (j+1) : ℝ) / ((j : ℝ) + 1)

def total (b : ℕ → ℤ) (n : ℕ) : ℤ := ∑ j ∈ range n, b (j+1)

theorem row_facts : ∀ h : Channel, ∀ t ∈ rows h,
    0 < t.d ∧ 0 < t.k ∧ t.d * t.k = q ∧
    ∀ j : Fin 105, char h (j.val + t.k) = char h j.val := by decide +kernel

theorem row_period {h : Channel} {t : Row} (ht : t ∈ rows h) :
    Function.Periodic (fun n => dilate (char h) t.d n) q := by
  obtain ⟨hd, _, hq, hper⟩ := row_facts h t ht
  have hk (m : ℕ) : char h (m + t.k) = char h m := by
    have hx := hper ⟨m % 105, Nat.mod_lt _ (by decide)⟩
    simpa [char, Nat.add_mod, Nat.mod_mod] using hx
  intro n
  have hdq : t.d ∣ q := ⟨t.k, hq.symm⟩
  by_cases hn : t.d ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [← hq, ← Nat.mul_add]
    simp [dilate, Nat.mul_div_cancel_left _ hd, hk]
  · have hnn : ¬ t.d ∣ n + q := fun z => hn ((Nat.dvd_add_left hdq).mp z)
    simp [dilate, hn, hnn]

theorem raw_period : Function.Periodic raw q := by
  intro n
  apply Finset.sum_congr rfl
  intro h _
  unfold part
  congr 1
  apply List.map_congr_left
  intro t ht
  exact congrArg (fun x => t.a * x) (row_period ht n)

theorem witness_period : Function.Periodic witness q := by
  intro n
  unfold witness
  rw [raw_period n]

theorem char_means : ∀ h : Channel, h ≠ 0 → total (char h) 105 = 0 := by decide +kernel

/-- Each channel's scaled coefficients add to zero. -/
theorem weights_cancel : ∀ h : Channel, ((rows h).map Row.w).sum = 0 := by decide +kernel

/-- Exponents in k = q/d. Only the principal channel needs three logarithmic moments. -/
def exponent (p k : ℕ) : ℕ := if p*p ∣ k then 2 else if p ∣ k then 1 else 0

theorem principal_factorizations : ∀ t ∈ rows 0,
    t.k = 3 ^ exponent 3 t.k * 5 ^ exponent 5 t.k * 7 ^ exponent 7 t.k := by decide +kernel

theorem moment3 : ((rows 0).map fun t => t.w * (exponent 3 t.k : ℤ)).sum = 0 := by decide +kernel
theorem moment5 : ((rows 0).map fun t => t.w * (exponent 5 t.k : ℤ)).sum = 0 := by decide +kernel
theorem moment7 : ((rows 0).map fun t => t.w * (exponent 7 t.k : ℤ)).sum = 0 := by decide +kernel

/-- One pass records the numerator sum and the sign condition in a block. -/
def scan (start : ℕ) : ℕ → ℤ × Bool
  | 0 => (0, true)
  | j+1 =>
    let a := scan start j
    let n := start+j+1
    let z := raw n
    (a.1 + z, a.2 && (if n = q then z == 0 else z == 2 || z == -2))

private theorem scan_sum (start n : ℕ) :
    (scan start n).1 = ∑ j ∈ range n, raw (start+j+1) := by
  induction n with
  | zero => simp [scan]
  | succ n ih => simp only [scan, sum_range_succ, ih]

private theorem scan_signs (start n : ℕ) (h : (scan start n).2 = true) (j : ℕ) (hj : j < n) :
    if start+j+1 = q then raw (start+j+1) = 0
    else raw (start+j+1) = 2 ∨ raw (start+j+1) = -2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [scan, Bool.and_eq_true] at h
    by_cases he : j = n
    · subst j
      split_ifs at h ⊢ with hz <;> simpa using h.2
    · exact ih h.1 (by omega)

def blockTotals : List ℤ := [
  14, -18, -6, 14, 2, 14, -10, -2, 6, -14, 10, -6, 6, 6, -10,
  2, -14, -2, 22, -10, 6, -6, -6, 2, -14, 22, -10, 6, 10, -14,
  2, -10, 6, 14, -6, 10, -22, -2, 14, -2, 10, -18, 6, 6, -18,
  10, 6, 6, 18, -6, 6, -14, -2, 14, -10, 6, -18, -6, 6, -6,
  18, -10, -2, 18, -10, -2, -10, 14, 14, -6, 10, -26, 2, 10, -6,
  10, -14, -6, 6, -14, 14, 2, 2, 6, -10, 6, -22, 2, 22, -6,
  14, -10, -10, 10, -6, 14, -10, -2, 10, -22, 2, -14, 14, 10, -12]

private theorem blocks_total_zero : blockTotals.sum = 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem block_certificate (i : Fin 105) :
    scan (105*i.val) 105 = (blockTotals[i.val]!, true) := by
  fin_cases i <;> decide +kernel

theorem raw_mean : total raw q = 0 := by
  have ht (k : ℕ) (hk : k ≤ 105) :
      total raw (105*k) = ∑ i ∈ range k, blockTotals[i]! := by
    induction k with
    | zero => simp [total]
    | succ k ih =>
      have hc := congrArg Prod.fst (block_certificate ⟨k, by omega⟩)
      have he : (scan (105*k) 105).1 = blockTotals[k]! := hc
      rw [scan_sum] at he
      change (∑ j ∈ range (105*(k+1)), raw (j+1)) = _
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ (f := fun i => blockTotals[i]!) k]
      change total raw (105*k) + _ = _ + _
      rw [ih (by omega), he]
  have hh := ht 105 (by decide)
  have hs : (∑ i ∈ range 105, blockTotals[i]!) = 0 := by decide +kernel
  exact hh.trans hs

private theorem periodic_mod {b : ℕ → ℤ} {p : ℕ} (hp : Function.Periodic b p) (n : ℕ) :
    b n = b (n % p) := by
  have aux (a k : ℕ) : b (a + k*p) = b a := by
    induction k with
    | zero => simp
    | succ k ih => simpa only [Nat.succ_mul, ← Nat.add_assoc, hp _] using ih
  calc b n = b (n % p + n / p * p) := by rw [Nat.mul_comm (n/p), Nat.mod_add_div]
       _ = _ := aux _ _

theorem raw_values (n : ℕ) : if q ∣ n then raw n = 0 else raw n = 2 ∨ raw n = -2 := by
  rw [periodic_mod raw_period n]
  by_cases hd : q ∣ n
  · simp only [hd, ite_true, Nat.mod_eq_zero_of_dvd hd]
    decide +kernel
  · rw [ite_eq_right hd]
    let r := n % q
    have hr0 : r ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
    have hr : r < 11025 := Nat.mod_lt _ (by decide)
    let i := (r-1)/105
    let j := (r-1)%105
    have hi : i < 105 := by dsimp [i]; omega
    have hj : j < 105 := Nat.mod_lt _ (by decide)
    have hs := congrArg Prod.snd (block_certificate ⟨i,hi⟩)
    have he := scan_signs (105*i) 105 hs j hj
    have hpos : 105*i+j+1 = r := by dsimp [i,j]; omega
    rw [hpos, ite_eq_right (show r ≠ q from Nat.ne_of_lt hr)] at he
    exact he

theorem witness_signs (n : ℕ) :
    if q ∣ n then witness n = 0 else witness n = 1 ∨ witness n = -1 := by
  have h := raw_values n
  unfold witness
  split_ifs at h ⊢ with hz
  · rw [h]; decide
  · rcases h with h | h <;> rw [h] <;> decide

theorem twice_witness (n : ℕ) : 2 * witness n = raw n := by
  have h := raw_values n
  unfold witness
  split_ifs at h
  · rw [h]; decide
  · rcases h with h | h <;> rw [h] <;> decide

private theorem total_add_period {b : ℕ → ℤ} {p : ℕ} (hp : Function.Periodic b p) (n : ℕ) :
    total b (n+p) = total b p + total b n := by
  rw [Nat.add_comm n p]
  unfold total
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show p + i + 1 = (i+1)+p by omega, hp]

/-- A zero-mean periodic coefficient sequence has convergent ordered harmonic sums. -/
theorem periodic_harmonic_converges {b : ℕ → ℤ} {p : ℕ} (hp0 : 0 < p)
    (hp : Function.Periodic b p) (hm : total b p = 0) :
    ∃ c : ℝ, Tendsto (partialL b) atTop (𝓝 c) := by
  have ht : Function.Periodic (total b) p := by intro n; rw [total_add_period hp, hm, zero_add]
  let B : ℝ := ∑ i ∈ range p, |(total b i : ℝ)|
  have hb (n : ℕ) : ‖∑ j ∈ range n, (b (j+1) : ℝ)‖ ≤ B := by
    rw [← Int.cast_sum, Real.norm_eq_abs]
    change |(total b n : ℝ)| ≤ B
    rw [periodic_mod ht n]
    exact Finset.single_le_sum (f := fun i => |(total b i : ℝ)|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.mod_lt n hp0))
  have ha : Antitone (fun n : ℕ => 1 / ((n:ℝ)+1)) := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete
    (ha.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hb)
  refine ⟨c, ?_⟩
  change Tendsto (fun n => ∑ j ∈ range n, (b (j+1) : ℝ) / ((j:ℝ)+1)) atTop (𝓝 c)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hc

private theorem nat_multiple_tendsto {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => k*n) atTop atTop := by
  apply tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk) tendsto_id

/-- Exact reindexing of the positive multiples of d, valid at every cutoff. -/
private theorem partial_dilate {d : ℕ} (_hd : 0 < d) (b : ℕ → ℤ) (N : ℕ) :
    partialL (dilate b d) N = (d : ℝ)⁻¹ * partialL b (N/d) := by
  induction N with
  | zero => simp [partialL]
  | succ n ih =>
    rw [show partialL (dilate b d) (n+1) = partialL (dilate b d) n +
          (dilate b d (n+1):ℝ) / ((n:ℝ)+1) by simp [partialL, Finset.sum_range_succ], ih]
    by_cases h : d ∣ n+1
    · have hdiv := Nat.succ_div_of_dvd h
      have hmul : (d : ℝ) * (↑(n / d) + 1 : ℝ) = ↑n + 1 := by
        exact_mod_cast (show d * (n / d + 1) = n+1 by rw [← hdiv, Nat.mul_div_cancel' h])
      simp only [dilate, ite_eq_left h, hdiv]
      rw [show partialL b (n/d + 1) = partialL b (n/d) +
          (b (n/d+1) : ℝ) / ((n/d : ℕ) + 1 : ℝ) by simp [partialL, Finset.sum_range_succ]]
      rw [mul_add]
      congr 1
      rw [← hmul, div_eq_mul_inv, mul_inv_rev]
      simp only [div_eq_mul_inv]
      ring
    · simp [dilate, h, Nat.succ_div_of_not_dvd h]

private theorem partial_add (b c : ℕ → ℤ) (N : ℕ) :
    partialL (fun n => b n + c n) N = partialL b N + partialL c N := by
  simp [partialL, add_div, Finset.sum_add_distrib]

private theorem partial_scale (a : ℤ) (b : ℕ → ℤ) (N : ℕ) :
    partialL (fun n => a * b n) N = (a:ℝ) * partialL b N := by
  simp [partialL, Finset.mul_sum, mul_div_assoc]

private theorem partial_rows (b : ℕ → ℤ) (rs : List Row)
    (facts : ∀ t ∈ rs, 0 < t.d ∧ t.d * t.k = q) (n : ℕ) :
    (q:ℝ) * partialL (part b rs) (q*n)
      = (rs.map fun t => (t.w:ℝ) * partialL b (t.k*n)).sum := by
  induction rs with
  | nil => simp [partialL, part]
  | cons t ts ih =>
    obtain ⟨hd, hq⟩ := facts t (by simp)
    have htail : ∀ v ∈ ts, 0 < v.d ∧ v.d * v.k = q := fun _ hv => facts _ (List.mem_cons_of_mem _ hv)
    have heq : part b (t :: ts) = fun m => t.a * dilate b t.d m + part b ts m := by
      funext m; simp [part]
    rw [heq, partial_add, mul_add, ih htail, partial_scale, partial_dilate hd]
    have hcut : q*n/t.d = t.k*n := by rw [← hq, Nat.mul_assoc, Nat.mul_div_cancel_left _ hd]
    simp only [List.map_cons, List.sum_cons, hcut]
    congr 1
    have hr : (t.d:ℝ) * (t.k:ℝ) = (q:ℝ) := by exact_mod_cast hq
    have hn : (t.d:ℝ) ≠ 0 := by positivity
    rw [← hr]
    simp only [Row.w, Int.cast_mul, Int.cast_natCast]
    field_simp

private noncomputable def weighted (rs : List Row) (v : Row → ℝ) : ℝ :=
  (rs.map fun t => (t.w : ℝ) * v t).sum

private theorem weighted_congr {rs : List Row} {u v : Row → ℝ}
    (h : ∀ t ∈ rs, u t = v t) : weighted rs u = weighted rs v := by
  unfold weighted
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [h t ht]

private theorem weighted_add (rs : List Row) (u v : Row → ℝ) :
    weighted rs (fun t => u t + v t) = weighted rs u + weighted rs v := by
  induction rs with
  | nil => simp [weighted]
  | cons t ts ih =>
    simp only [weighted, List.map_cons, List.sum_cons, mul_add] at ih ⊢
    linarith

private theorem weighted_sub (rs : List Row) (u v : Row → ℝ) :
    weighted rs (fun t => u t - v t) = weighted rs u - weighted rs v := by
  induction rs with
  | nil => simp [weighted]
  | cons t ts ih =>
    simp only [weighted, List.map_cons, List.sum_cons, mul_sub] at ih ⊢
    linarith

private theorem weighted_const (rs : List Row) (c : ℝ) :
    weighted rs (fun _ => c) = (((rs.map Row.w).sum : ℤ):ℝ) * c := by
  induction rs with
  | nil => simp [weighted]
  | cons t ts ih =>
    simp only [weighted, List.map_cons, List.sum_cons, Int.cast_add, add_mul] at ih ⊢
    rw [ih]

private theorem weighted_moment (rs : List Row) (p : ℕ) (c : ℝ) :
    weighted rs (fun t => (exponent p t.k : ℝ) * c) =
      ((((rs.map fun t => t.w * (exponent p t.k : ℤ)).sum) : ℤ):ℝ) * c := by
  induction rs with
  | nil => simp [weighted]
  | cons t ts ih =>
    simp only [weighted, List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      add_mul] at ih ⊢
    rw [ih]; ring

private theorem weighted_tendsto (rs : List Row) (u : ℕ → Row → ℝ) (v : Row → ℝ)
    (h : ∀ t ∈ rs, Tendsto (fun n => u n t) atTop (𝓝 (v t))) :
    Tendsto (fun n => weighted rs (u n)) atTop (𝓝 (weighted rs v)) := by
  induction rs with
  | nil => simp [weighted]
  | cons t ts ih =>
    exact ((h t (by simp)).const_mul _).add (ih (fun r hr => h r (List.mem_cons_of_mem t hr)))

private theorem principal_log_sum :
    weighted (rows 0) (fun t => Real.log t.k) = 0 := by
  have ht {t : Row} (h : t ∈ rows 0) :
      Real.log t.k = (exponent 3 t.k : ℝ)*Real.log 3 +
          (exponent 5 t.k : ℝ)*Real.log 5 + (exponent 7 t.k : ℝ)*Real.log 7 := by
    have hc : (t.k : ℝ) = (3:ℝ) ^ exponent 3 t.k * 5 ^ exponent 5 t.k * 7 ^ exponent 7 t.k := by
      exact_mod_cast principal_factorizations t h
    rw [hc, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
  calc
    _ = weighted (rows 0) (fun t => (exponent 3 t.k : ℝ) * Real.log 3 +
          (exponent 5 t.k : ℝ) * Real.log 5 + (exponent 7 t.k : ℝ) * Real.log 7) :=
      weighted_congr (fun _ h => ht h)
    _ = _ := by rw [weighted_add, weighted_add, weighted_moment, weighted_moment, weighted_moment,
                     moment3, moment5, moment7]; norm_num

private theorem principal_harmonic (n : ℕ) : partialL (char 0) n = (harmonic n : ℝ) := by
  induction n with
  | zero => simp [partialL]
  | succ n ih =>
    simp only [partialL, Finset.sum_range_succ, char_zero, Int.cast_one] at ih ⊢
    rw [ih, harmonic_succ]
    push_cast
    simp [one_div]

private theorem centered_harmonic {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => partialL (char 0) (k*n) - Real.log n) atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log k)) := by
  apply ((Real.tendsto_harmonic_sub_log.comp (nat_multiple_tendsto hk)).add_const
    (Real.log k)).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  simp only [Function.comp_apply, principal_harmonic, Nat.cast_mul]
  rw [Real.log_mul (by positivity) (by positivity)]
  ring

private theorem component_limit (h : Channel) :
    Tendsto (fun n : ℕ => weighted (rows h) (fun t => partialL (char h) (t.k*n))) atTop (𝓝 0) := by
  by_cases hz : h = 0
  · subst h
    have H := weighted_tendsto (rows 0)
      (fun n t => partialL (char 0) (t.k*n) - Real.log n)
      (fun t => Real.eulerMascheroniConstant + Real.log t.k)
      (fun t ht => centered_harmonic (row_facts 0 t ht).2.1)
    have hh (n : ℕ) : weighted (rows 0) (fun t => partialL (char 0) (t.k*n) - Real.log n) =
        weighted (rows 0) (fun t => partialL (char 0) (t.k*n)) := by
      rw [weighted_sub, weighted_const, weights_cancel]; simp
    have hl : weighted (rows 0) (fun t => Real.eulerMascheroniConstant + Real.log t.k) = 0 := by
      rw [weighted_add, weighted_const, weights_cancel, principal_log_sum]; simp
    simpa only [hh,hl] using H
  · obtain ⟨c, hc⟩ := periodic_harmonic_converges (by decide : 0 < 105) (char_period h) (char_means h hz)
    have H := weighted_tendsto (rows h) (fun n t => partialL (char h) (t.k*n)) (fun _ => c)
      (fun t ht => hc.comp (nat_multiple_tendsto (row_facts h t ht).2.1))
    simpa only [weighted_const, weights_cancel, Int.cast_zero, zero_mul] using H

private theorem full_blocks (n : ℕ) :
    (q:ℝ) * partialL raw (q*n) =
      ∑ h : Channel, weighted (rows h) (fun t => partialL (char h) (t.k*n)) := by
  have hs : partialL raw (q*n) = ∑ h : Channel, partialL (part (char h) (rows h)) (q*n) := by
    simp only [partialL, raw, Int.cast_sum, Finset.sum_div]
    rw [Finset.sum_comm]
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  exact partial_rows _ _ (fun t ht => ⟨(row_facts h t ht).1, (row_facts h t ht).2.2.1⟩) _

theorem raw_vanishes : Tendsto (partialL raw) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := periodic_harmonic_converges (by decide : 0 < q) raw_period raw_mean
  have hsum := tendsto_finsetSum (s := (Finset.univ : Finset Channel))
    (fun h _ => component_limit h)
  have hzero : Tendsto (fun n : ℕ => (q:ℝ) * partialL raw (q*n)) atTop (𝓝 0) := by
    simpa only [full_blocks, Finset.sum_const_zero] using hsum
  have he : (q:ℝ) * c = 0 :=
    tendsto_nhds_unique ((hc.comp (nat_multiple_tendsto (by decide : 0 < q))).const_mul (q:ℝ)) hzero
  have hc0 : c = 0 := (mul_eq_zero.mp he).resolve_left (by norm_num)
  simpa only [hc0] using hc

theorem witness_vanishes : Tendsto (partialL witness) atTop (𝓝 0) := by
  have he (n : ℕ) : partialL witness n = (1/2 : ℝ) * partialL raw n := by
    have hr : raw = fun m => 2 * witness m := funext (fun m => (twice_witness m).symm)
    rw [hr, partial_scale]
    push_cast
    ring
  simpa only [← he, mul_zero] using raw_vanishes.const_mul (1/2:ℝ)

/-- The explicit counterexample, including every positive index of the ordinary partial sums. -/
theorem counterexample :
    Function.Periodic witness 11025 ∧
    (∀ n, 11025 ∣ n → witness n = 0) ∧
    (∀ n, ¬11025 ∣ n → witness n = 1 ∨ witness n = -1) ∧
    Tendsto (fun N : ℕ => ∑ j ∈ range N, (witness (j+1) : ℝ) / ((j:ℝ)+1))
      atTop (𝓝 0) := by
  refine ⟨witness_period, ?_, ?_, witness_vanishes⟩
  · intro n h; simpa [h] using witness_signs n
  · intro n h; simpa [h] using witness_signs n

/-- Every admissible periodic harmonic series fails to converge to zero (Erdős). -/
def ErdosNonvanishing : Prop := ∀ (p : ℕ), 2 ≤ p → ∀ (b : ℕ → ℤ),
  Function.Periodic b p → (∀ n, p ∣ n → b n = 0) →
  (∀ n, ¬p ∣ n → b n = 1 ∨ b n = -1) →
  ¬ Tendsto (fun N : ℕ => ∑ j ∈ range N, (b (j+1) : ℝ) / ((j:ℝ)+1)) atTop (𝓝 0)

theorem not_erdosNonvanishing : ¬ ErdosNonvanishing := by
  intro h
  obtain ⟨hp, hz, hs, hv⟩ := counterexample
  exact h 11025 (by decide) witness hp hz hs hv

#print axioms ErdosLSeries.not_erdosNonvanishing

end ErdosLSeries
