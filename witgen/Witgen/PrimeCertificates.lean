import Witgen.Primality

namespace Witgen.PrimeCertificates
open Witgen.Primality

theorem prime_2 : Nat.Prime 2 := by decide

theorem prime_3 : Nat.Prime 3 := by decide

theorem prime_7 : Nat.Prime 7 := by decide

theorem prime_5 : Nat.Prime 5 := by decide

private def trace_13441_full : List PowStep := [
  (3, 1331),
  (4, 10461),
  (8, 11944),
  (0, 1)]

private theorem power_13441_full : (11 : ZMod 13441) ^ 13440 = 1 :=
  trace_power 13441 11 13440 1 trace_13441_full
    (by decide) (by decide) (by decide)

private def trace_13441_2 : List PowStep := [
  (1, 11),
  (10, 6740),
  (4, 1193),
  (0, 13440)]

private theorem power_13441_2 : (11 : ZMod 13441) ^ 6720 ≠ 1 :=
  trace_power_ne_one 13441 11 6720 13440 trace_13441_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_13441_3 : List PowStep := [
  (1, 11),
  (1, 369),
  (8, 12675),
  (0, 645)]

private theorem power_13441_3 : (11 : ZMod 13441) ^ 4480 ≠ 1 :=
  trace_power_ne_one 13441 11 4480 645 trace_13441_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_13441_5 : List PowStep := [
  (10, 4317),
  (8, 8845),
  (0, 8733)]

private theorem power_13441_5 : (11 : ZMod 13441) ^ 2688 ≠ 1 :=
  trace_power_ne_one 13441 11 2688 8733 trace_13441_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_13441_7 : List PowStep := [
  (7, 11162),
  (8, 11503),
  (0, 10662)]

private theorem power_13441_7 : (11 : ZMod 13441) ^ 1920 ≠ 1 :=
  trace_power_ne_one 13441 11 1920 10662 trace_13441_7
    (by decide) (by decide) (by decide) (by decide)

theorem prime_13441 : Nat.Prime 13441 := by
  let factors : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 5, 7]
  have hf : factors.prod = 13441 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_7, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (11 : ZMod 13441) ^ ((13441 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 2) ≠ 1 from power_13441_2), (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 2) ≠ 1 from power_13441_2), (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 2) ≠ 1 from power_13441_2), (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 2) ≠ 1 from power_13441_2), (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 2) ≠ 1 from power_13441_2), (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 2) ≠ 1 from power_13441_2), (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 2) ≠ 1 from power_13441_2), (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 3) ≠ 1 from power_13441_3), (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 5) ≠ 1 from power_13441_5), (List.forall_mem_cons.mpr ⟨(show (11 : ZMod 13441) ^ ((13441 - 1) / 7) ≠ 1 from power_13441_7), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 13441 (11 : ZMod 13441) power_13441_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_29 : Nat.Prime 29 := by decide

theorem prime_31 : Nat.Prime 31 := by decide

theorem prime_11 : Nat.Prime 11 := by decide

theorem prime_13 : Nat.Prime 13 := by decide

private def trace_7723_full : List PowStep := [
  (1, 3),
  (14, 4700),
  (2, 4481),
  (10, 1)]

private theorem power_7723_full : (3 : ZMod 7723) ^ 7722 = 1 :=
  trace_power 7723 3 7722 1 trace_7723_full
    (by decide) (by decide) (by decide)

private def trace_7723_2 : List PowStep := [
  (15, 7296),
  (1, 3912),
  (5, 7722)]

private theorem power_7723_2 : (3 : ZMod 7723) ^ 3861 ≠ 1 :=
  trace_power_ne_one 7723 3 3861 7722 trace_7723_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_7723_3 : List PowStep := [
  (10, 4988),
  (0, 1572),
  (14, 917)]

private theorem power_7723_3 : (3 : ZMod 7723) ^ 2574 ≠ 1 :=
  trace_power_ne_one 7723 3 2574 917 trace_7723_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_7723_11 : List PowStep := [
  (2, 9),
  (11, 120),
  (14, 2429)]

private theorem power_7723_11 : (3 : ZMod 7723) ^ 702 ≠ 1 :=
  trace_power_ne_one 7723 3 702 2429 trace_7723_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_7723_13 : List PowStep := [
  (2, 9),
  (5, 7310),
  (2, 2889)]

private theorem power_7723_13 : (3 : ZMod 7723) ^ 594 ≠ 1 :=
  trace_power_ne_one 7723 3 594 2889 trace_7723_13
    (by decide) (by decide) (by decide) (by decide)

theorem prime_7723 : Nat.Prime 7723 := by
  let factors : List Nat := [2, 3, 3, 3, 11, 13]
  have hf : factors.prod = 7723 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_13, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 7723) ^ ((7723 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 7723) ^ ((7723 - 1) / 2) ≠ 1 from power_7723_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 7723) ^ ((7723 - 1) / 3) ≠ 1 from power_7723_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 7723) ^ ((7723 - 1) / 3) ≠ 1 from power_7723_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 7723) ^ ((7723 - 1) / 3) ≠ 1 from power_7723_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 7723) ^ ((7723 - 1) / 11) ≠ 1 from power_7723_11), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 7723) ^ ((7723 - 1) / 13) ≠ 1 from power_7723_13), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 7723 (3 : ZMod 7723) power_7723_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_17 : Nat.Prime 17 := by decide

private def trace_443_full : List PowStep := [
  (1, 2),
  (11, 246),
  (10, 1)]

private theorem power_443_full : (2 : ZMod 443) ^ 442 = 1 :=
  trace_power 443 2 442 1 trace_443_full
    (by decide) (by decide) (by decide)

private def trace_443_2 : List PowStep := [
  (13, 218),
  (13, 442)]

private theorem power_443_2 : (2 : ZMod 443) ^ 221 ≠ 1 :=
  trace_power_ne_one 443 2 221 442 trace_443_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_443_13 : List PowStep := [
  (2, 4),
  (2, 35)]

private theorem power_443_13 : (2 : ZMod 443) ^ 34 ≠ 1 :=
  trace_power_ne_one 443 2 34 35 trace_443_13
    (by decide) (by decide) (by decide) (by decide)

private def trace_443_17 : List PowStep := [
  (1, 2),
  (10, 123)]

private theorem power_443_17 : (2 : ZMod 443) ^ 26 ≠ 1 :=
  trace_power_ne_one 443 2 26 123 trace_443_17
    (by decide) (by decide) (by decide) (by decide)

theorem prime_443 : Nat.Prime 443 := by
  let factors : List Nat := [2, 13, 17]
  have hf : factors.prod = 443 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_13, (List.forall_mem_cons.mpr ⟨prime_17, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 443) ^ ((443 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 443) ^ ((443 - 1) / 2) ≠ 1 from power_443_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 443) ^ ((443 - 1) / 13) ≠ 1 from power_443_13), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 443) ^ ((443 - 1) / 17) ≠ 1 from power_443_17), by simp⟩)⟩)⟩)
  apply lucas_primality 443 (2 : ZMod 443) power_443_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_887_full : List PowStep := [
  (3, 125),
  (7, 412),
  (6, 1)]

private theorem power_887_full : (5 : ZMod 887) ^ 886 = 1 :=
  trace_power 887 5 886 1 trace_887_full
    (by decide) (by decide) (by decide)

private def trace_887_2 : List PowStep := [
  (1, 5),
  (11, 322),
  (11, 886)]

private theorem power_887_2 : (5 : ZMod 887) ^ 443 ≠ 1 :=
  trace_power_ne_one 887 5 443 886 trace_887_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_887_443 : List PowStep := [
  (2, 25)]

private theorem power_887_443 : (5 : ZMod 887) ^ 2 ≠ 1 :=
  trace_power_ne_one 887 5 2 25 trace_887_443
    (by decide) (by decide) (by decide) (by decide)

theorem prime_887 : Nat.Prime 887 := by
  let factors : List Nat := [2, 443]
  have hf : factors.prod = 887 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_443, by simp⟩)⟩)
  have hn : ∀ q ∈ factors, (5 : ZMod 887) ^ ((887 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 887) ^ ((887 - 1) / 2) ≠ 1 from power_887_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 887) ^ ((887 - 1) / 443) ≠ 1 from power_887_443), by simp⟩)⟩)
  apply lucas_primality 887 (5 : ZMod 887) power_887_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_5323_full : List PowStep := [
  (1, 5),
  (4, 4124),
  (12, 2319),
  (10, 1)]

private theorem power_5323_full : (5 : ZMod 5323) ^ 5322 = 1 :=
  trace_power 5323 5 5322 1 trace_5323_full
    (by decide) (by decide) (by decide)

private def trace_5323_2 : List PowStep := [
  (10, 3243),
  (6, 4614),
  (5, 5322)]

private theorem power_5323_2 : (5 : ZMod 5323) ^ 2661 ≠ 1 :=
  trace_power_ne_one 5323 5 2661 5322 trace_5323_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_5323_3 : List PowStep := [
  (6, 4979),
  (14, 3294),
  (14, 1282)]

private theorem power_5323_3 : (5 : ZMod 5323) ^ 1774 ≠ 1 :=
  trace_power_ne_one 5323 5 1774 1282 trace_5323_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_5323_887 : List PowStep := [
  (6, 4979)]

private theorem power_5323_887 : (5 : ZMod 5323) ^ 6 ≠ 1 :=
  trace_power_ne_one 5323 5 6 4979 trace_5323_887
    (by decide) (by decide) (by decide) (by decide)

theorem prime_5323 : Nat.Prime 5323 := by
  let factors : List Nat := [2, 3, 887]
  have hf : factors.prod = 5323 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_887, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (5 : ZMod 5323) ^ ((5323 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 5323) ^ ((5323 - 1) / 2) ≠ 1 from power_5323_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 5323) ^ ((5323 - 1) / 3) ≠ 1 from power_5323_3), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 5323) ^ ((5323 - 1) / 887) ≠ 1 from power_5323_887), by simp⟩)⟩)⟩)
  apply lucas_primality 5323 (5 : ZMod 5323) power_5323_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_131_full : List PowStep := [
  (8, 125),
  (2, 1)]

private theorem power_131_full : (2 : ZMod 131) ^ 130 = 1 :=
  trace_power 131 2 130 1 trace_131_full
    (by decide) (by decide) (by decide)

private def trace_131_2 : List PowStep := [
  (4, 16),
  (1, 130)]

private theorem power_131_2 : (2 : ZMod 131) ^ 65 ≠ 1 :=
  trace_power_ne_one 131 2 65 130 trace_131_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_131_5 : List PowStep := [
  (1, 2),
  (10, 53)]

private theorem power_131_5 : (2 : ZMod 131) ^ 26 ≠ 1 :=
  trace_power_ne_one 131 2 26 53 trace_131_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_131_13 : List PowStep := [
  (10, 107)]

private theorem power_131_13 : (2 : ZMod 131) ^ 10 ≠ 1 :=
  trace_power_ne_one 131 2 10 107 trace_131_13
    (by decide) (by decide) (by decide) (by decide)

theorem prime_131 : Nat.Prime 131 := by
  let factors : List Nat := [2, 5, 13]
  have hf : factors.prod = 131 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_13, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 131) ^ ((131 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 131) ^ ((131 - 1) / 2) ≠ 1 from power_131_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 131) ^ ((131 - 1) / 5) ≠ 1 from power_131_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 131) ^ ((131 - 1) / 13) ≠ 1 from power_131_13), by simp⟩)⟩)⟩)
  apply lucas_primality 131 (2 : ZMod 131) power_131_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_2621_full : List PowStep := [
  (10, 1024),
  (3, 662),
  (12, 1)]

private theorem power_2621_full : (2 : ZMod 2621) ^ 2620 = 1 :=
  trace_power 2621 2 2620 1 trace_2621_full
    (by decide) (by decide) (by decide)

private def trace_2621_2 : List PowStep := [
  (5, 32),
  (1, 2340),
  (14, 2620)]

private theorem power_2621_2 : (2 : ZMod 2621) ^ 1310 ≠ 1 :=
  trace_power_ne_one 2621 2 1310 2620 trace_2621_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_2621_5 : List PowStep := [
  (2, 4),
  (0, 121),
  (12, 1860)]

private theorem power_2621_5 : (2 : ZMod 2621) ^ 524 ≠ 1 :=
  trace_power_ne_one 2621 2 524 1860 trace_2621_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_2621_131 : List PowStep := [
  (1, 2),
  (4, 176)]

private theorem power_2621_131 : (2 : ZMod 2621) ^ 20 ≠ 1 :=
  trace_power_ne_one 2621 2 20 176 trace_2621_131
    (by decide) (by decide) (by decide) (by decide)

theorem prime_2621 : Nat.Prime 2621 := by
  let factors : List Nat := [2, 2, 5, 131]
  have hf : factors.prod = 2621 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_131, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 2621) ^ ((2621 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 2621) ^ ((2621 - 1) / 2) ≠ 1 from power_2621_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 2621) ^ ((2621 - 1) / 2) ≠ 1 from power_2621_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 2621) ^ ((2621 - 1) / 5) ≠ 1 from power_2621_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 2621) ^ ((2621 - 1) / 131) ≠ 1 from power_2621_131), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 2621 (2 : ZMod 2621) power_2621_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_24809_full : List PowStep := [
  (6, 21847),
  (0, 19968),
  (14, 6374),
  (8, 1)]

private theorem power_24809_full : (6 : ZMod 24809) ^ 24808 = 1 :=
  trace_power 24809 6 24808 1 trace_24809_full
    (by decide) (by decide) (by decide)

private def trace_24809_2 : List PowStep := [
  (3, 216),
  (0, 1849),
  (7, 6979),
  (4, 24808)]

private theorem power_24809_2 : (6 : ZMod 24809) ^ 12404 ≠ 1 :=
  trace_power_ne_one 24809 6 12404 24808 trace_24809_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_24809_7 : List PowStep := [
  (13, 20775),
  (13, 5170),
  (8, 13134)]

private theorem power_24809_7 : (6 : ZMod 24809) ^ 3544 ≠ 1 :=
  trace_power_ne_one 24809 6 3544 13134 trace_24809_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_24809_443 : List PowStep := [
  (3, 216),
  (8, 19364)]

private theorem power_24809_443 : (6 : ZMod 24809) ^ 56 ≠ 1 :=
  trace_power_ne_one 24809 6 56 19364 trace_24809_443
    (by decide) (by decide) (by decide) (by decide)

theorem prime_24809 : Nat.Prime 24809 := by
  let factors : List Nat := [2, 2, 2, 7, 443]
  have hf : factors.prod = 24809 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_443, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (6 : ZMod 24809) ^ ((24809 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 24809) ^ ((24809 - 1) / 2) ≠ 1 from power_24809_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 24809) ^ ((24809 - 1) / 2) ≠ 1 from power_24809_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 24809) ^ ((24809 - 1) / 2) ≠ 1 from power_24809_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 24809) ^ ((24809 - 1) / 7) ≠ 1 from power_24809_7), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 24809) ^ ((24809 - 1) / 443) ≠ 1 from power_24809_443), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 24809 (6 : ZMod 24809) power_24809_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_97 : Nat.Prime 97 := by decide

private def trace_971_full : List PowStep := [
  (3, 216),
  (12, 676),
  (10, 1)]

private theorem power_971_full : (6 : ZMod 971) ^ 970 = 1 :=
  trace_power 971 6 970 1 trace_971_full
    (by decide) (by decide) (by decide)

private def trace_971_2 : List PowStep := [
  (1, 6),
  (14, 945),
  (5, 970)]

private theorem power_971_2 : (6 : ZMod 971) ^ 485 ≠ 1 :=
  trace_power_ne_one 971 6 485 970 trace_971_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_971_5 : List PowStep := [
  (12, 362),
  (2, 341)]

private theorem power_971_5 : (6 : ZMod 971) ^ 194 ≠ 1 :=
  trace_power_ne_one 971 6 194 341 trace_971_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_971_97 : List PowStep := [
  (10, 64)]

private theorem power_971_97 : (6 : ZMod 971) ^ 10 ≠ 1 :=
  trace_power_ne_one 971 6 10 64 trace_971_97
    (by decide) (by decide) (by decide) (by decide)

theorem prime_971 : Nat.Prime 971 := by
  let factors : List Nat := [2, 5, 97]
  have hf : factors.prod = 971 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_97, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (6 : ZMod 971) ^ ((971 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 971) ^ ((971 - 1) / 2) ≠ 1 from power_971_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 971) ^ ((971 - 1) / 5) ≠ 1 from power_971_5), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 971) ^ ((971 - 1) / 97) ≠ 1 from power_971_97), by simp⟩)⟩)⟩)
  apply lucas_primality 971 (6 : ZMod 971) power_971_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_1373_full : List PowStep := [
  (5, 32),
  (5, 730),
  (12, 1)]

private theorem power_1373_full : (2 : ZMod 1373) ^ 1372 = 1 :=
  trace_power 1373 2 1372 1 trace_1373_full
    (by decide) (by decide) (by decide)

private def trace_1373_2 : List PowStep := [
  (2, 4),
  (10, 1176),
  (14, 1372)]

private theorem power_1373_2 : (2 : ZMod 1373) ^ 686 ≠ 1 :=
  trace_power_ne_one 1373 2 686 1372 trace_1373_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_1373_7 : List PowStep := [
  (12, 1350),
  (4, 333)]

private theorem power_1373_7 : (2 : ZMod 1373) ^ 196 ≠ 1 :=
  trace_power_ne_one 1373 2 196 333 trace_1373_7
    (by decide) (by decide) (by decide) (by decide)

theorem prime_1373 : Nat.Prime 1373 := by
  let factors : List Nat := [2, 2, 7, 7, 7]
  have hf : factors.prod = 1373 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_7, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 1373) ^ ((1373 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1373) ^ ((1373 - 1) / 2) ≠ 1 from power_1373_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1373) ^ ((1373 - 1) / 2) ≠ 1 from power_1373_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1373) ^ ((1373 - 1) / 7) ≠ 1 from power_1373_7), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1373) ^ ((1373 - 1) / 7) ≠ 1 from power_1373_7), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1373) ^ ((1373 - 1) / 7) ≠ 1 from power_1373_7), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 1373 (2 : ZMod 1373) power_1373_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_13331831_full : List PowStep := [
  (12, 3862938),
  (11, 579455),
  (6, 4106094),
  (13, 9868366),
  (7, 5990386),
  (6, 1)]

private theorem power_13331831_full : (13 : ZMod 13331831) ^ 13331830 = 1 :=
  trace_power 13331831 13 13331830 1 trace_13331831_full
    (by decide) (by decide) (by decide)

private def trace_13331831_2 : List PowStep := [
  (6, 4826809),
  (5, 7714091),
  (11, 6065882),
  (6, 2631949),
  (11, 9702145),
  (11, 13331830)]

private theorem power_13331831_2 : (13 : ZMod 13331831) ^ 6665915 ≠ 1 :=
  trace_power_ne_one 13331831 13 6665915 13331830 trace_13331831_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_13331831_5 : List PowStep := [
  (2, 169),
  (8, 10922529),
  (10, 4020997),
  (15, 12833409),
  (7, 9131488),
  (14, 1325729)]

private theorem power_13331831_5 : (13 : ZMod 13331831) ^ 2666366 ≠ 1 :=
  trace_power_ne_one 13331831 13 2666366 1325729 trace_13331831_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_13331831_971 : List PowStep := [
  (3, 2197),
  (5, 10584135),
  (10, 7353757),
  (2, 54862)]

private theorem power_13331831_971 : (13 : ZMod 13331831) ^ 13730 ≠ 1 :=
  trace_power_ne_one 13331831 13 13730 54862 trace_13331831_971
    (by decide) (by decide) (by decide) (by decide)

private def trace_13331831_1373 : List PowStep := [
  (2, 169),
  (5, 2929843),
  (14, 12728949),
  (14, 1273336)]

private theorem power_13331831_1373 : (13 : ZMod 13331831) ^ 9710 ≠ 1 :=
  trace_power_ne_one 13331831 13 9710 1273336 trace_13331831_1373
    (by decide) (by decide) (by decide) (by decide)

theorem prime_13331831 : Nat.Prime 13331831 := by
  let factors : List Nat := [2, 5, 971, 1373]
  have hf : factors.prod = 13331831 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_971, (List.forall_mem_cons.mpr ⟨prime_1373, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (13 : ZMod 13331831) ^ ((13331831 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (13 : ZMod 13331831) ^ ((13331831 - 1) / 2) ≠ 1 from power_13331831_2), (List.forall_mem_cons.mpr ⟨(show (13 : ZMod 13331831) ^ ((13331831 - 1) / 5) ≠ 1 from power_13331831_5), (List.forall_mem_cons.mpr ⟨(show (13 : ZMod 13331831) ^ ((13331831 - 1) / 971) ≠ 1 from power_13331831_971), (List.forall_mem_cons.mpr ⟨(show (13 : ZMod 13331831) ^ ((13331831 - 1) / 1373) ≠ 1 from power_13331831_1373), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 13331831 (13 : ZMod 13331831) power_13331831_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_173378833005251801_full : List PowStep := [
  (2, 36),
  (6, 21790213715291578),
  (7, 99677234139541764),
  (15, 3368371542926353),
  (7, 76458030845387095),
  (2, 2661272309587633),
  (1, 22310760199776093),
  (4, 8945667638686208),
  (8, 106266323974470520),
  (13, 147259584550412958),
  (9, 62055906959727409),
  (8, 149182325374317383),
  (12, 8989695441841755),
  (13, 78874395206344160),
  (8, 1)]

private theorem power_173378833005251801_full : (6 : ZMod 173378833005251801) ^ 173378833005251800 = 1 :=
  trace_power 173378833005251801 6 173378833005251800 1 trace_173378833005251801_full
    (by decide) (by decide) (by decide)

private def trace_173378833005251801_2 : List PowStep := [
  (1, 6),
  (3, 609359740010496),
  (3, 81913997771873158),
  (15, 162842939938862840),
  (11, 24739794834396214),
  (9, 116250703612390386),
  (0, 67639182480645959),
  (10, 168000095251595091),
  (4, 4719366651816589),
  (6, 158029331887384211),
  (12, 41620882897807259),
  (12, 56723074198269176),
  (6, 139888048562341300),
  (6, 91107143042781314),
  (12, 173378833005251800)]

private theorem power_173378833005251801_2 : (6 : ZMod 173378833005251801) ^ 86689416502625900 ≠ 1 :=
  trace_power_ne_one 173378833005251801 6 86689416502625900 173378833005251800 trace_173378833005251801_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_173378833005251801_5 : List PowStep := [
  (7, 279936),
  (11, 133874754874154071),
  (3, 122648021250026591),
  (1, 159651781424345506),
  (6, 102033018611972657),
  (13, 73656779507683574),
  (0, 80762642891003281),
  (14, 159459602849152774),
  (9, 69177802672993588),
  (1, 17645794912245610),
  (14, 21052025694001250),
  (8, 163988916079117421),
  (15, 53214408687627019),
  (8, 152071994513768143)]

private theorem power_173378833005251801_5 : (6 : ZMod 173378833005251801) ^ 34675766601050360 ≠ 1 :=
  trace_power_ne_one 173378833005251801 6 34675766601050360 152071994513768143 trace_173378833005251801_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_173378833005251801_2621 : List PowStep := [
  (3, 216),
  (12, 159269880826956384),
  (2, 19402838721209279),
  (9, 96617079509322298),
  (11, 162029924808990403),
  (8, 34904794565063304),
  (0, 30718264939569301),
  (11, 156487354477526135),
  (0, 25844936888514986),
  (5, 35704728358093799),
  (11, 108120047587878250),
  (8, 25743935490785551)]

private theorem power_173378833005251801_2621 : (6 : ZMod 173378833005251801) ^ 66149879055800 ≠ 1 :=
  trace_power_ne_one 173378833005251801 6 66149879055800 25743935490785551 trace_173378833005251801_2621
    (by decide) (by decide) (by decide) (by decide)

private def trace_173378833005251801_24809 : List PowStep := [
  (6, 46656),
  (5, 147568151895467569),
  (11, 64276270095161665),
  (2, 68041318676577048),
  (5, 105834587299047740),
  (12, 170583569438012863),
  (10, 80524939449454298),
  (5, 55644608874959136),
  (15, 119459330269932367),
  (1, 106676457829610737),
  (8, 5978649957832462)]

private theorem power_173378833005251801_24809 : (6 : ZMod 173378833005251801) ^ 6988545810200 ≠ 1 :=
  trace_power_ne_one 173378833005251801 6 6988545810200 5978649957832462 trace_173378833005251801_24809
    (by decide) (by decide) (by decide) (by decide)

private def trace_173378833005251801_13331831 : List PowStep := [
  (3, 216),
  (0, 128517149041441353),
  (7, 59907746556209881),
  (2, 121178055310358369),
  (6, 86609252493878995),
  (10, 95103685589455660),
  (15, 153204516969474565),
  (14, 128747721422986148),
  (8, 17954474104786666)]

private theorem power_173378833005251801_13331831 : (6 : ZMod 173378833005251801) ^ 13004877800 ≠ 1 :=
  trace_power_ne_one 173378833005251801 6 13004877800 17954474104786666 trace_173378833005251801_13331831
    (by decide) (by decide) (by decide) (by decide)

theorem prime_173378833005251801 : Nat.Prime 173378833005251801 := by
  let factors : List Nat := [2, 2, 2, 5, 5, 2621, 24809, 13331831]
  have hf : factors.prod = 173378833005251801 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_2621, (List.forall_mem_cons.mpr ⟨prime_24809, (List.forall_mem_cons.mpr ⟨prime_13331831, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 2) ≠ 1 from power_173378833005251801_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 2) ≠ 1 from power_173378833005251801_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 2) ≠ 1 from power_173378833005251801_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 5) ≠ 1 from power_173378833005251801_5), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 5) ≠ 1 from power_173378833005251801_5), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 2621) ≠ 1 from power_173378833005251801_2621), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 24809) ≠ 1 from power_173378833005251801_24809), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 173378833005251801) ^ ((173378833005251801 - 1) / 13331831) ≠ 1 from power_173378833005251801_13331831), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 173378833005251801 (6 : ZMod 173378833005251801) power_173378833005251801_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_22149492674086928081353_full : List PowStep := [
  (4, 625),
  (11, 20265429543367072715235),
  (0, 15014219458920908773029),
  (11, 3558965754464197193599),
  (9, 12947889361189007801800),
  (15, 14463504609737887962596),
  (5, 16358301642006669673187),
  (9, 2947349116315036109797),
  (10, 6617593180135275994007),
  (0, 6855500453254494898541),
  (10, 6681994500969066780150),
  (5, 1670580035486115775143),
  (4, 10472249993016399035441),
  (5, 11644232534919459002658),
  (7, 18441480332362396846448),
  (6, 9039697795203049330663),
  (1, 19434835822220207762908),
  (12, 20522624947140711830193),
  (8, 1)]

private theorem power_22149492674086928081353_full : (5 : ZMod 22149492674086928081353) ^ 22149492674086928081352 = 1 :=
  trace_power 22149492674086928081353 5 22149492674086928081352 1 trace_22149492674086928081353_full
    (by decide) (by decide) (by decide)

private def trace_22149492674086928081353_2 : List PowStep := [
  (2, 25),
  (5, 20642200132787214039873),
  (8, 11875576125201398349080),
  (5, 19044262405409840974412),
  (12, 10438229056133636852413),
  (15, 14493069211751173937351),
  (10, 7569797415146976999632),
  (12, 17762549822534567264948),
  (13, 1447209750251943197947),
  (0, 296522981392269404078),
  (5, 4879892411730754318756),
  (2, 21308988234200175869852),
  (10, 8126066616462735956168),
  (2, 5368879661716537262487),
  (11, 15210306949354592684621),
  (11, 315100390030515540483),
  (0, 19219358909941727999983),
  (14, 19793272015330214601985),
  (4, 22149492674086928081352)]

private theorem power_22149492674086928081353_2 : (5 : ZMod 22149492674086928081353) ^ 11074746337043464040676 ≠ 1 :=
  trace_power_ne_one 22149492674086928081353 5 11074746337043464040676 22149492674086928081352 trace_22149492674086928081353_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_22149492674086928081353_3 : List PowStep := [
  (1, 5),
  (9, 298023223876953125),
  (0, 9853314600575142283596),
  (3, 14912490295617092338205),
  (13, 17434592184979910407944),
  (15, 341104998951469101034),
  (12, 12094550725037039816500),
  (8, 11280863161696812243809),
  (8, 2014701297440464015400),
  (10, 16645228654935978020153),
  (14, 12603264242846537981847),
  (1, 17297066712593144771268),
  (12, 9251989960790626043325),
  (1, 16618909245204328962890),
  (13, 8382327546187229863003),
  (2, 2778956895890618448845),
  (0, 6418338355953360177926),
  (9, 1896509684782274034369),
  (8, 10043889752229528935999)]

private theorem power_22149492674086928081353_3 : (5 : ZMod 22149492674086928081353) ^ 7383164224695642693784 ≠ 1 :=
  trace_power_ne_one 22149492674086928081353 5 7383164224695642693784 10043889752229528935999 trace_22149492674086928081353_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_22149492674086928081353_5323 : List PowStep := [
  (3, 125),
  (9, 18537270794265601671234),
  (11, 4046078577459148213167),
  (15, 13469809407088453896100),
  (2, 17500750783550146290518),
  (11, 11758593072468035278549),
  (1, 9734040606146427920917),
  (14, 1139888170716566736099),
  (13, 4342484607011090675294),
  (4, 4518556584198592282814),
  (6, 282427676547347577074),
  (5, 1249022104893752696491),
  (3, 21549976347289770038777),
  (4, 3525433051026096839049),
  (5, 4343097984374542695874),
  (8, 6446620476143922066636)]

private theorem power_22149492674086928081353_5323 : (5 : ZMod 22149492674086928081353) ^ 4161091992126043224 ≠ 1 :=
  trace_power_ne_one 22149492674086928081353 5 4161091992126043224 6446620476143922066636 trace_22149492674086928081353_5323
    (by decide) (by decide) (by decide) (by decide)

private def trace_22149492674086928081353_173378833005251801 : List PowStep := [
  (1, 5),
  (15, 4656612873077392578125),
  (3, 16225548480503155183026),
  (0, 21751691058198768458756),
  (8, 317195385910872261254)]

private theorem power_22149492674086928081353_173378833005251801 : (5 : ZMod 22149492674086928081353) ^ 127752 ≠ 1 :=
  trace_power_ne_one 22149492674086928081353 5 127752 317195385910872261254 trace_22149492674086928081353_173378833005251801
    (by decide) (by decide) (by decide) (by decide)

theorem prime_22149492674086928081353 : Nat.Prime 22149492674086928081353 := by
  let factors : List Nat := [2, 2, 2, 3, 5323, 173378833005251801]
  have hf : factors.prod = 22149492674086928081353 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5323, (List.forall_mem_cons.mpr ⟨prime_173378833005251801, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 2) ≠ 1 from power_22149492674086928081353_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 2) ≠ 1 from power_22149492674086928081353_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 2) ≠ 1 from power_22149492674086928081353_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 3) ≠ 1 from power_22149492674086928081353_3), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 5323) ≠ 1 from power_22149492674086928081353_5323), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 22149492674086928081353) ^ ((22149492674086928081353 - 1) / 173378833005251801) ≠ 1 from power_22149492674086928081353_173378833005251801), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 22149492674086928081353 (5 : ZMod 22149492674086928081353) power_22149492674086928081353_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_132896956044521568488119_full : List PowStep := [
  (1, 6),
  (12, 6140942214464815497216),
  (2, 109902895880040747200032),
  (4, 13195632222390385846741),
  (5, 21432587412947966203691),
  (11, 75248751594973012570069),
  (12, 121189579412827235665216),
  (1, 93432416054882468262962),
  (9, 812528268590005082850),
  (12, 60888289486259611969959),
  (3, 96959711894015058627891),
  (13, 95031126513578272202614),
  (15, 97881712414666661740313),
  (10, 56527286504140716369939),
  (0, 85164851068492117450075),
  (12, 1843779721739006483559),
  (4, 54596190338619025067418),
  (10, 37090816713675380502732),
  (11, 10680123675250291832538),
  (6, 1)]

private theorem power_132896956044521568488119_full : (6 : ZMod 132896956044521568488119) ^ 132896956044521568488118 = 1 :=
  trace_power 132896956044521568488119 6 132896956044521568488118 1 trace_132896956044521568488119_full
    (by decide) (by decide) (by decide)

private def trace_132896956044521568488119_2 : List PowStep := [
  (14, 78364164096),
  (1, 122789243140463099928409),
  (2, 25756179227066249763362),
  (2, 126576072113474597537706),
  (13, 114758044651612000197712),
  (14, 99969185935380378506290),
  (0, 16799907836733710060378),
  (12, 118944971639787541467845),
  (14, 72734756699851493753566),
  (1, 77534531119421959813251),
  (14, 16835202334238216167727),
  (15, 35400723987692606045496),
  (13, 61451828168486922974778),
  (0, 59704721610524402651938),
  (6, 1185017263014692940835),
  (2, 126661106826275938330915),
  (5, 55828291466482996598283),
  (5, 34168063199283984733468),
  (11, 132896956044521568488118)]

private theorem power_132896956044521568488119_2 : (6 : ZMod 132896956044521568488119) ^ 66448478022260784244059 ≠ 1 :=
  trace_power_ne_one 132896956044521568488119 6 66448478022260784244059 132896956044521568488118 trace_132896956044521568488119_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_132896956044521568488119_3 : List PowStep := [
  (9, 10077696),
  (6, 132717731879155890604823),
  (1, 17238636564558505586917),
  (7, 54719789286159230904871),
  (3, 3409616873814744080888),
  (14, 44148545806395241113743),
  (11, 58572868985768943138530),
  (3, 60979868235474042624143),
  (4, 71896509454829889736702),
  (1, 97188728776804121082324),
  (4, 101112960406948362818174),
  (10, 74988660404382215957201),
  (8, 79050220917618110373877),
  (10, 41963351768298629561938),
  (14, 81374867682781041554445),
  (12, 69967760094259517567316),
  (3, 13708315974789577555584),
  (9, 35019642108680367496727),
  (2, 76725380987433565404982)]

private theorem power_132896956044521568488119_3 : (6 : ZMod 132896956044521568488119) ^ 44298985348173856162706 ≠ 1 :=
  trace_power_ne_one 132896956044521568488119 6 44298985348173856162706 76725380987433565404982 trace_132896956044521568488119_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_132896956044521568488119_22149492674086928081353 : List PowStep := [
  (6, 46656)]

private theorem power_132896956044521568488119_22149492674086928081353 : (6 : ZMod 132896956044521568488119) ^ 6 ≠ 1 :=
  trace_power_ne_one 132896956044521568488119 6 6 46656 trace_132896956044521568488119_22149492674086928081353
    (by decide) (by decide) (by decide) (by decide)

theorem prime_132896956044521568488119 : Nat.Prime 132896956044521568488119 := by
  let factors : List Nat := [2, 3, 22149492674086928081353]
  have hf : factors.prod = 132896956044521568488119 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_22149492674086928081353, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (6 : ZMod 132896956044521568488119) ^ ((132896956044521568488119 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 132896956044521568488119) ^ ((132896956044521568488119 - 1) / 2) ≠ 1 from power_132896956044521568488119_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 132896956044521568488119) ^ ((132896956044521568488119 - 1) / 3) ≠ 1 from power_132896956044521568488119_3), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 132896956044521568488119) ^ ((132896956044521568488119 - 1) / 22149492674086928081353) ≠ 1 from power_132896956044521568488119_22149492674086928081353), by simp⟩)⟩)⟩)
  apply lucas_primality 132896956044521568488119 (6 : ZMod 132896956044521568488119) power_132896956044521568488119_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_271_full : List PowStep := [
  (1, 6),
  (0, 138),
  (14, 1)]

private theorem power_271_full : (6 : ZMod 271) ^ 270 = 1 :=
  trace_power 271 6 270 1 trace_271_full
    (by decide) (by decide) (by decide)

private def trace_271_2 : List PowStep := [
  (8, 229),
  (7, 270)]

private theorem power_271_2 : (6 : ZMod 271) ^ 135 ≠ 1 :=
  trace_power_ne_one 271 6 135 270 trace_271_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_271_3 : List PowStep := [
  (5, 188),
  (10, 242)]

private theorem power_271_3 : (6 : ZMod 271) ^ 90 ≠ 1 :=
  trace_power_ne_one 271 6 90 242 trace_271_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_271_5 : List PowStep := [
  (3, 216),
  (6, 10)]

private theorem power_271_5 : (6 : ZMod 271) ^ 54 ≠ 1 :=
  trace_power_ne_one 271 6 54 10 trace_271_5
    (by decide) (by decide) (by decide) (by decide)

theorem prime_271 : Nat.Prime 271 := by
  let factors : List Nat := [2, 3, 3, 3, 5]
  have hf : factors.prod = 271 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (6 : ZMod 271) ^ ((271 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 271) ^ ((271 - 1) / 2) ≠ 1 from power_271_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 271) ^ ((271 - 1) / 3) ≠ 1 from power_271_3), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 271) ^ ((271 - 1) / 3) ≠ 1 from power_271_3), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 271) ^ ((271 - 1) / 3) ≠ 1 from power_271_3), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 271) ^ ((271 - 1) / 5) ≠ 1 from power_271_5), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 271 (6 : ZMod 271) power_271_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_1627_full : List PowStep := [
  (6, 729),
  (5, 73),
  (10, 1)]

private theorem power_1627_full : (3 : ZMod 1627) ^ 1626 = 1 :=
  trace_power 1627 3 1626 1 trace_1627_full
    (by decide) (by decide) (by decide)

private def trace_1627_2 : List PowStep := [
  (3, 27),
  (2, 787),
  (13, 1626)]

private theorem power_1627_2 : (3 : ZMod 1627) ^ 813 ≠ 1 :=
  trace_power_ne_one 1627 3 813 1626 trace_1627_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_1627_3 : List PowStep := [
  (2, 9),
  (1, 220),
  (14, 1362)]

private theorem power_1627_3 : (3 : ZMod 1627) ^ 542 ≠ 1 :=
  trace_power_ne_one 1627 3 542 1362 trace_1627_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_1627_271 : List PowStep := [
  (6, 729)]

private theorem power_1627_271 : (3 : ZMod 1627) ^ 6 ≠ 1 :=
  trace_power_ne_one 1627 3 6 729 trace_1627_271
    (by decide) (by decide) (by decide) (by decide)

theorem prime_1627 : Nat.Prime 1627 := by
  let factors : List Nat := [2, 3, 271]
  have hf : factors.prod = 1627 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_271, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 1627) ^ ((1627 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1627) ^ ((1627 - 1) / 2) ≠ 1 from power_1627_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1627) ^ ((1627 - 1) / 3) ≠ 1 from power_1627_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1627) ^ ((1627 - 1) / 271) ≠ 1 from power_1627_271), by simp⟩)⟩)⟩)
  apply lucas_primality 1627 (3 : ZMod 1627) power_1627_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_83 : Nat.Prime 83 := by decide

private def trace_2657_full : List PowStep := [
  (10, 595),
  (6, 169),
  (0, 1)]

private theorem power_2657_full : (3 : ZMod 2657) ^ 2656 = 1 :=
  trace_power 2657 3 2656 1 trace_2657_full
    (by decide) (by decide) (by decide)

private def trace_2657_2 : List PowStep := [
  (5, 243),
  (3, 2644),
  (0, 2656)]

private theorem power_2657_2 : (3 : ZMod 2657) ^ 1328 ≠ 1 :=
  trace_power_ne_one 2657 3 1328 2656 trace_2657_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_2657_83 : List PowStep := [
  (2, 9),
  (0, 2491)]

private theorem power_2657_83 : (3 : ZMod 2657) ^ 32 ≠ 1 :=
  trace_power_ne_one 2657 3 32 2491 trace_2657_83
    (by decide) (by decide) (by decide) (by decide)

theorem prime_2657 : Nat.Prime 2657 := by
  let factors : List Nat := [2, 2, 2, 2, 2, 83]
  have hf : factors.prod = 2657 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_83, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 2657) ^ ((2657 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2657) ^ ((2657 - 1) / 2) ≠ 1 from power_2657_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2657) ^ ((2657 - 1) / 2) ≠ 1 from power_2657_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2657) ^ ((2657 - 1) / 2) ≠ 1 from power_2657_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2657) ^ ((2657 - 1) / 2) ≠ 1 from power_2657_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2657) ^ ((2657 - 1) / 2) ≠ 1 from power_2657_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2657) ^ ((2657 - 1) / 83) ≠ 1 from power_2657_83), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 2657 (3 : ZMod 2657) power_2657_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_67 : Nat.Prime 67 := by decide

private def trace_4423_full : List PowStep := [
  (1, 3),
  (1, 1832),
  (4, 305),
  (6, 1)]

private theorem power_4423_full : (3 : ZMod 4423) ^ 4422 = 1 :=
  trace_power 4423 3 4422 1 trace_4423_full
    (by decide) (by decide) (by decide)

private def trace_4423_2 : List PowStep := [
  (8, 2138),
  (10, 2014),
  (3, 4422)]

private theorem power_4423_2 : (3 : ZMod 4423) ^ 2211 ≠ 1 :=
  trace_power_ne_one 4423 3 2211 4422 trace_4423_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_4423_3 : List PowStep := [
  (5, 243),
  (12, 817),
  (2, 66)]

private theorem power_4423_3 : (3 : ZMod 4423) ^ 1474 ≠ 1 :=
  trace_power_ne_one 4423 3 1474 66 trace_4423_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_4423_11 : List PowStep := [
  (1, 3),
  (9, 2461),
  (2, 285)]

private theorem power_4423_11 : (3 : ZMod 4423) ^ 402 ≠ 1 :=
  trace_power_ne_one 4423 3 402 285 trace_4423_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_4423_67 : List PowStep := [
  (4, 81),
  (2, 4365)]

private theorem power_4423_67 : (3 : ZMod 4423) ^ 66 ≠ 1 :=
  trace_power_ne_one 4423 3 66 4365 trace_4423_67
    (by decide) (by decide) (by decide) (by decide)

theorem prime_4423 : Nat.Prime 4423 := by
  let factors : List Nat := [2, 3, 11, 67]
  have hf : factors.prod = 4423 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_67, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 4423) ^ ((4423 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 4423) ^ ((4423 - 1) / 2) ≠ 1 from power_4423_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 4423) ^ ((4423 - 1) / 3) ≠ 1 from power_4423_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 4423) ^ ((4423 - 1) / 11) ≠ 1 from power_4423_11), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 4423) ^ ((4423 - 1) / 67) ≠ 1 from power_4423_67), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 4423 (3 : ZMod 4423) power_4423_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_103_full : List PowStep := [
  (6, 72),
  (6, 1)]

private theorem power_103_full : (5 : ZMod 103) ^ 102 = 1 :=
  trace_power 103 5 102 1 trace_103_full
    (by decide) (by decide) (by decide)

private def trace_103_2 : List PowStep := [
  (3, 22),
  (3, 102)]

private theorem power_103_2 : (5 : ZMod 103) ^ 51 ≠ 1 :=
  trace_power_ne_one 103 5 51 102 trace_103_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_103_3 : List PowStep := [
  (2, 25),
  (2, 56)]

private theorem power_103_3 : (5 : ZMod 103) ^ 34 ≠ 1 :=
  trace_power_ne_one 103 5 34 56 trace_103_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_103_17 : List PowStep := [
  (6, 72)]

private theorem power_103_17 : (5 : ZMod 103) ^ 6 ≠ 1 :=
  trace_power_ne_one 103 5 6 72 trace_103_17
    (by decide) (by decide) (by decide) (by decide)

theorem prime_103 : Nat.Prime 103 := by
  let factors : List Nat := [2, 3, 17]
  have hf : factors.prod = 103 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_17, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (5 : ZMod 103) ^ ((103 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 103) ^ ((103 - 1) / 2) ≠ 1 from power_103_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 103) ^ ((103 - 1) / 3) ≠ 1 from power_103_3), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 103) ^ ((103 - 1) / 17) ≠ 1 from power_103_17), by simp⟩)⟩)⟩)
  apply lucas_primality 103 (5 : ZMod 103) power_103_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_41201_full : List PowStep := [
  (10, 17848),
  (0, 1793),
  (15, 914),
  (0, 1)]

private theorem power_41201_full : (3 : ZMod 41201) ^ 41200 = 1 :=
  trace_power 41201 3 41200 1 trace_41201_full
    (by decide) (by decide) (by decide)

private def trace_41201_2 : List PowStep := [
  (5, 243),
  (0, 5855),
  (7, 15502),
  (8, 41200)]

private theorem power_41201_2 : (3 : ZMod 41201) ^ 20600 ≠ 1 :=
  trace_power_ne_one 41201 3 20600 41200 trace_41201_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_41201_5 : List PowStep := [
  (2, 9),
  (0, 30095),
  (3, 7782),
  (0, 18549)]

private theorem power_41201_5 : (3 : ZMod 41201) ^ 8240 ≠ 1 :=
  trace_power_ne_one 41201 3 8240 18549 trace_41201_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_41201_103 : List PowStep := [
  (1, 3),
  (9, 15085),
  (0, 16839)]

private theorem power_41201_103 : (3 : ZMod 41201) ^ 400 ≠ 1 :=
  trace_power_ne_one 41201 3 400 16839 trace_41201_103
    (by decide) (by decide) (by decide) (by decide)

theorem prime_41201 : Nat.Prime 41201 := by
  let factors : List Nat := [2, 2, 2, 2, 5, 5, 103]
  have hf : factors.prod = 41201 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_103, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 41201) ^ ((41201 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 41201) ^ ((41201 - 1) / 2) ≠ 1 from power_41201_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 41201) ^ ((41201 - 1) / 2) ≠ 1 from power_41201_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 41201) ^ ((41201 - 1) / 2) ≠ 1 from power_41201_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 41201) ^ ((41201 - 1) / 2) ≠ 1 from power_41201_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 41201) ^ ((41201 - 1) / 5) ≠ 1 from power_41201_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 41201) ^ ((41201 - 1) / 5) ≠ 1 from power_41201_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 41201) ^ ((41201 - 1) / 103) ≠ 1 from power_41201_103), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 41201 (3 : ZMod 41201) power_41201_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_101_full : List PowStep := [
  (6, 64),
  (4, 1)]

private theorem power_101_full : (2 : ZMod 101) ^ 100 = 1 :=
  trace_power 101 2 100 1 trace_101_full
    (by decide) (by decide) (by decide)

private def trace_101_2 : List PowStep := [
  (3, 8),
  (2, 100)]

private theorem power_101_2 : (2 : ZMod 101) ^ 50 ≠ 1 :=
  trace_power_ne_one 101 2 50 100 trace_101_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_101_5 : List PowStep := [
  (1, 2),
  (4, 95)]

private theorem power_101_5 : (2 : ZMod 101) ^ 20 ≠ 1 :=
  trace_power_ne_one 101 2 20 95 trace_101_5
    (by decide) (by decide) (by decide) (by decide)

theorem prime_101 : Nat.Prime 101 := by
  let factors : List Nat := [2, 2, 5, 5]
  have hf : factors.prod = 101 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 101) ^ ((101 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 101) ^ ((101 - 1) / 2) ≠ 1 from power_101_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 101) ^ ((101 - 1) / 2) ≠ 1 from power_101_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 101) ^ ((101 - 1) / 5) ≠ 1 from power_101_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 101) ^ ((101 - 1) / 5) ≠ 1 from power_101_5), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 101 (2 : ZMod 101) power_101_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_239_full : List PowStep := [
  (14, 211),
  (14, 1)]

private theorem power_239_full : (7 : ZMod 239) ^ 238 = 1 :=
  trace_power 239 7 238 1 trace_239_full
    (by decide) (by decide) (by decide)

private def trace_239_2 : List PowStep := [
  (7, 188),
  (7, 238)]

private theorem power_239_2 : (7 : ZMod 239) ^ 119 ≠ 1 :=
  trace_power_ne_one 239 7 119 238 trace_239_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_239_7 : List PowStep := [
  (2, 49),
  (2, 24)]

private theorem power_239_7 : (7 : ZMod 239) ^ 34 ≠ 1 :=
  trace_power_ne_one 239 7 34 24 trace_239_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_239_17 : List PowStep := [
  (14, 211)]

private theorem power_239_17 : (7 : ZMod 239) ^ 14 ≠ 1 :=
  trace_power_ne_one 239 7 14 211 trace_239_17
    (by decide) (by decide) (by decide) (by decide)

theorem prime_239 : Nat.Prime 239 := by
  let factors : List Nat := [2, 7, 17]
  have hf : factors.prod = 239 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_17, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (7 : ZMod 239) ^ ((239 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 239) ^ ((239 - 1) / 2) ≠ 1 from power_239_2), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 239) ^ ((239 - 1) / 7) ≠ 1 from power_239_7), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 239) ^ ((239 - 1) / 17) ≠ 1 from power_239_17), by simp⟩)⟩)⟩)
  apply lucas_primality 239 (7 : ZMod 239) power_239_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_96557_full : List PowStep := [
  (1, 2),
  (7, 84706),
  (9, 89775),
  (2, 46323),
  (12, 1)]

private theorem power_96557_full : (2 : ZMod 96557) ^ 96556 = 1 :=
  trace_power 96557 2 96556 1 trace_96557_full
    (by decide) (by decide) (by decide)

private def trace_96557_2 : List PowStep := [
  (11, 2048),
  (12, 30722),
  (9, 21381),
  (6, 96556)]

private theorem power_96557_2 : (2 : ZMod 96557) ^ 48278 ≠ 1 :=
  trace_power_ne_one 96557 2 48278 96556 trace_96557_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_96557_101 : List PowStep := [
  (3, 8),
  (11, 13493),
  (12, 63065)]

private theorem power_96557_101 : (2 : ZMod 96557) ^ 956 ≠ 1 :=
  trace_power_ne_one 96557 2 956 63065 trace_96557_101
    (by decide) (by decide) (by decide) (by decide)

private def trace_96557_239 : List PowStep := [
  (1, 2),
  (9, 49153),
  (4, 29586)]

private theorem power_96557_239 : (2 : ZMod 96557) ^ 404 ≠ 1 :=
  trace_power_ne_one 96557 2 404 29586 trace_96557_239
    (by decide) (by decide) (by decide) (by decide)

theorem prime_96557 : Nat.Prime 96557 := by
  let factors : List Nat := [2, 2, 101, 239]
  have hf : factors.prod = 96557 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_101, (List.forall_mem_cons.mpr ⟨prime_239, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 96557) ^ ((96557 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 96557) ^ ((96557 - 1) / 2) ≠ 1 from power_96557_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 96557) ^ ((96557 - 1) / 2) ≠ 1 from power_96557_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 96557) ^ ((96557 - 1) / 101) ≠ 1 from power_96557_101), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 96557) ^ ((96557 - 1) / 239) ≠ 1 from power_96557_239), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 96557 (2 : ZMod 96557) power_96557_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_19 : Nat.Prime 19 := by decide

private def trace_419_full : List PowStep := [
  (1, 2),
  (10, 148),
  (2, 1)]

private theorem power_419_full : (2 : ZMod 419) ^ 418 = 1 :=
  trace_power 419 2 418 1 trace_419_full
    (by decide) (by decide) (by decide)

private def trace_419_2 : List PowStep := [
  (13, 231),
  (1, 418)]

private theorem power_419_2 : (2 : ZMod 419) ^ 209 ≠ 1 :=
  trace_power_ne_one 419 2 209 418 trace_419_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_419_11 : List PowStep := [
  (2, 4),
  (6, 334)]

private theorem power_419_11 : (2 : ZMod 419) ^ 38 ≠ 1 :=
  trace_power_ne_one 419 2 38 334 trace_419_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_419_19 : List PowStep := [
  (1, 2),
  (6, 114)]

private theorem power_419_19 : (2 : ZMod 419) ^ 22 ≠ 1 :=
  trace_power_ne_one 419 2 22 114 trace_419_19
    (by decide) (by decide) (by decide) (by decide)

theorem prime_419 : Nat.Prime 419 := by
  let factors : List Nat := [2, 11, 19]
  have hf : factors.prod = 419 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_19, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 419) ^ ((419 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 419) ^ ((419 - 1) / 2) ≠ 1 from power_419_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 419) ^ ((419 - 1) / 11) ≠ 1 from power_419_11), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 419) ^ ((419 - 1) / 19) ≠ 1 from power_419_19), by simp⟩)⟩)⟩)
  apply lucas_primality 419 (2 : ZMod 419) power_419_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_20113_full : List PowStep := [
  (4, 10000),
  (14, 5284),
  (9, 18435),
  (0, 1)]

private theorem power_20113_full : (10 : ZMod 20113) ^ 20112 = 1 :=
  trace_power 20113 10 20112 1 trace_20113_full
    (by decide) (by decide) (by decide)

private def trace_20113_2 : List PowStep := [
  (2, 100),
  (7, 2538),
  (4, 16600),
  (8, 20112)]

private theorem power_20113_2 : (10 : ZMod 20113) ^ 10056 ≠ 1 :=
  trace_power_ne_one 20113 10 10056 20112 trace_20113_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_20113_3 : List PowStep := [
  (1, 10),
  (10, 14010),
  (3, 1655),
  (0, 5472)]

private theorem power_20113_3 : (10 : ZMod 20113) ^ 6704 ≠ 1 :=
  trace_power_ne_one 20113 10 6704 5472 trace_20113_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_20113_419 : List PowStep := [
  (3, 1000),
  (0, 4141)]

private theorem power_20113_419 : (10 : ZMod 20113) ^ 48 ≠ 1 :=
  trace_power_ne_one 20113 10 48 4141 trace_20113_419
    (by decide) (by decide) (by decide) (by decide)

theorem prime_20113 : Nat.Prime 20113 := by
  let factors : List Nat := [2, 2, 2, 2, 3, 419]
  have hf : factors.prod = 20113 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_419, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (10 : ZMod 20113) ^ ((20113 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 20113) ^ ((20113 - 1) / 2) ≠ 1 from power_20113_2), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 20113) ^ ((20113 - 1) / 2) ≠ 1 from power_20113_2), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 20113) ^ ((20113 - 1) / 2) ≠ 1 from power_20113_2), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 20113) ^ ((20113 - 1) / 2) ≠ 1 from power_20113_2), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 20113) ^ ((20113 - 1) / 3) ≠ 1 from power_20113_3), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 20113) ^ ((20113 - 1) / 419) ≠ 1 from power_20113_419), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 20113 (10 : ZMod 20113) power_20113_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_1206781_full : List PowStep := [
  (1, 10),
  (2, 404897),
  (6, 1052525),
  (9, 807530),
  (15, 736161),
  (12, 1)]

private theorem power_1206781_full : (10 : ZMod 1206781) ^ 1206780 = 1 :=
  trace_power 1206781 10 1206780 1 trace_1206781_full
    (by decide) (by decide) (by decide)

private def trace_1206781_2 : List PowStep := [
  (9, 785332),
  (3, 104908),
  (4, 1084374),
  (15, 1107724),
  (14, 1206780)]

private theorem power_1206781_2 : (10 : ZMod 1206781) ^ 603390 ≠ 1 :=
  trace_power_ne_one 1206781 10 603390 1206780 trace_1206781_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_1206781_3 : List PowStep := [
  (6, 1000000),
  (2, 167893),
  (3, 286873),
  (5, 76714),
  (4, 608272)]

private theorem power_1206781_3 : (10 : ZMod 1206781) ^ 402260 ≠ 1 :=
  trace_power_ne_one 1206781 10 402260 608272 trace_1206781_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_1206781_5 : List PowStep := [
  (3, 1000),
  (10, 250240),
  (14, 988517),
  (12, 560717),
  (12, 1065415)]

private theorem power_1206781_5 : (10 : ZMod 1206781) ^ 241356 ≠ 1 :=
  trace_power_ne_one 1206781 10 241356 1065415 trace_1206781_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_1206781_20113 : List PowStep := [
  (3, 1000),
  (12, 888380)]

private theorem power_1206781_20113 : (10 : ZMod 1206781) ^ 60 ≠ 1 :=
  trace_power_ne_one 1206781 10 60 888380 trace_1206781_20113
    (by decide) (by decide) (by decide) (by decide)

theorem prime_1206781 : Nat.Prime 1206781 := by
  let factors : List Nat := [2, 2, 3, 5, 20113]
  have hf : factors.prod = 1206781 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_20113, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (10 : ZMod 1206781) ^ ((1206781 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 1206781) ^ ((1206781 - 1) / 2) ≠ 1 from power_1206781_2), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 1206781) ^ ((1206781 - 1) / 2) ≠ 1 from power_1206781_2), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 1206781) ^ ((1206781 - 1) / 3) ≠ 1 from power_1206781_3), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 1206781) ^ ((1206781 - 1) / 5) ≠ 1 from power_1206781_5), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 1206781) ^ ((1206781 - 1) / 20113) ≠ 1 from power_1206781_20113), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 1206781 (10 : ZMod 1206781) power_1206781_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_7240687_full : List PowStep := [
  (6, 729),
  (14, 3212754),
  (7, 815003),
  (11, 2432736),
  (14, 5916734),
  (14, 1)]

private theorem power_7240687_full : (3 : ZMod 7240687) ^ 7240686 = 1 :=
  trace_power 7240687 3 7240686 1 trace_7240687_full
    (by decide) (by decide) (by decide)

private def trace_7240687_2 : List PowStep := [
  (3, 27),
  (7, 1828098),
  (3, 2058596),
  (13, 4000029),
  (15, 7008917),
  (7, 7240686)]

private theorem power_7240687_2 : (3 : ZMod 7240687) ^ 3620343 ≠ 1 :=
  trace_power_ne_one 7240687 3 3620343 7240686 trace_7240687_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_7240687_3 : List PowStep := [
  (2, 9),
  (4, 2975294),
  (13, 2902959),
  (3, 1123742),
  (15, 3243785),
  (10, 6501936)]

private theorem power_7240687_3 : (3 : ZMod 7240687) ^ 2413562 ≠ 1 :=
  trace_power_ne_one 7240687 3 2413562 6501936 trace_7240687_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_7240687_1206781 : List PowStep := [
  (6, 729)]

private theorem power_7240687_1206781 : (3 : ZMod 7240687) ^ 6 ≠ 1 :=
  trace_power_ne_one 7240687 3 6 729 trace_7240687_1206781
    (by decide) (by decide) (by decide) (by decide)

theorem prime_7240687 : Nat.Prime 7240687 := by
  let factors : List Nat := [2, 3, 1206781]
  have hf : factors.prod = 7240687 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_1206781, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 7240687) ^ ((7240687 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 7240687) ^ ((7240687 - 1) / 2) ≠ 1 from power_7240687_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 7240687) ^ ((7240687 - 1) / 3) ≠ 1 from power_7240687_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 7240687) ^ ((7240687 - 1) / 1206781) ≠ 1 from power_7240687_1206781), by simp⟩)⟩)⟩)
  apply lucas_primality 7240687 (3 : ZMod 7240687) power_7240687_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_53 : Nat.Prime 53 := by decide

private def trace_107590001_full : List PowStep := [
  (6, 729),
  (6, 62920633),
  (9, 21032378),
  (11, 17147185),
  (1, 10734825),
  (7, 11862917),
  (0, 1)]

private theorem power_107590001_full : (3 : ZMod 107590001) ^ 107590000 = 1 :=
  trace_power 107590001 3 107590000 1 trace_107590001_full
    (by decide) (by decide) (by decide)

private def trace_107590001_2 : List PowStep := [
  (3, 27),
  (3, 89750755),
  (4, 98399651),
  (13, 92888009),
  (8, 12979422),
  (11, 74833457),
  (8, 107590000)]

private theorem power_107590001_2 : (3 : ZMod 107590001) ^ 53795000 ≠ 1 :=
  trace_power_ne_one 107590001 3 53795000 107590000 trace_107590001_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_107590001_5 : List PowStep := [
  (1, 3),
  (4, 43904369),
  (8, 63631810),
  (5, 22580674),
  (6, 73739944),
  (11, 64382403),
  (0, 67174630)]

private theorem power_107590001_5 : (3 : ZMod 107590001) ^ 21518000 ≠ 1 :=
  trace_power_ne_one 107590001 3 21518000 67174630 trace_107590001_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_107590001_7 : List PowStep := [
  (14, 4782969),
  (10, 9527367),
  (8, 7456834),
  (7, 7445058),
  (1, 26305423),
  (0, 37492364)]

private theorem power_107590001_7 : (3 : ZMod 107590001) ^ 15370000 ≠ 1 :=
  trace_power_ne_one 107590001 3 15370000 37492364 trace_107590001_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_107590001_29 : List PowStep := [
  (3, 27),
  (8, 76253263),
  (9, 17447085),
  (12, 60667114),
  (3, 67918627),
  (0, 32711690)]

private theorem power_107590001_29 : (3 : ZMod 107590001) ^ 3710000 ≠ 1 :=
  trace_power_ne_one 107590001 3 3710000 32711690 trace_107590001_29
    (by decide) (by decide) (by decide) (by decide)

private def trace_107590001_53 : List PowStep := [
  (1, 3),
  (14, 20420985),
  (15, 63671192),
  (9, 81935824),
  (11, 48841791),
  (0, 15240736)]

private theorem power_107590001_53 : (3 : ZMod 107590001) ^ 2030000 ≠ 1 :=
  trace_power_ne_one 107590001 3 2030000 15240736 trace_107590001_53
    (by decide) (by decide) (by decide) (by decide)

theorem prime_107590001 : Nat.Prime 107590001 := by
  let factors : List Nat := [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53]
  have hf : factors.prod = 107590001 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_29, (List.forall_mem_cons.mpr ⟨prime_53, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 107590001) ^ ((107590001 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 2) ≠ 1 from power_107590001_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 2) ≠ 1 from power_107590001_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 2) ≠ 1 from power_107590001_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 2) ≠ 1 from power_107590001_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 5) ≠ 1 from power_107590001_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 5) ≠ 1 from power_107590001_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 5) ≠ 1 from power_107590001_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 5) ≠ 1 from power_107590001_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 7) ≠ 1 from power_107590001_7), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 29) ≠ 1 from power_107590001_29), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107590001) ^ ((107590001 - 1) / 53) ≠ 1 from power_107590001_53), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 107590001 (3 : ZMod 107590001) power_107590001_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_255515944373312847190720520512484175977_full : List PowStep := [
  (12, 531441),
  (0, 29530757701057884023829642930935549676),
  (3, 169370732391857245969895334087052081396),
  (10, 79716174543849707823105575972018106498),
  (9, 49187645109607076586238034147710821388),
  (4, 219236835492465487912168423673372651111),
  (11, 70804624184563327612246741573805853908),
  (2, 223568192645085876696095981147870545356),
  (13, 212007719781293929518820093449660728702),
  (3, 26426131869758825142814285120068914228),
  (14, 126828720038413691633082396893951346858),
  (6, 141965714162396576751412984526292467729),
  (4, 88369426337805496522430654468902520629),
  (4, 236609021026614482351799790349214640789),
  (1, 252472905046965328337639186249456290906),
  (9, 121167996399553842142396041982602598431),
  (10, 131554686227729553030715800814433666254),
  (0, 200153039591887114643012105749475409681),
  (5, 245946768731202040253206144601168505379),
  (12, 16988784633134836047334202269341922110),
  (13, 157701005066555249611705827334598298627),
  (8, 93899643026798086341536151938506308000),
  (12, 111097685949464779340891803632096918567),
  (12, 31354924605790841835682865686551094273),
  (11, 27395308716818440122128918235906694316),
  (15, 8637199352108785713758251257693765116),
  (9, 204031551689721771629775745213702469089),
  (8, 163075437672184139821549219002800949993),
  (7, 157981925543279121960841402103145361449),
  (0, 161936679795175458933915901328389379879),
  (6, 198673325022833988689104100400429175926),
  (8, 1)]

private theorem power_255515944373312847190720520512484175977_full : (3 : ZMod 255515944373312847190720520512484175977) ^ 255515944373312847190720520512484175976 = 1 :=
  trace_power 255515944373312847190720520512484175977 3 255515944373312847190720520512484175976 1 trace_255515944373312847190720520512484175977_full
    (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_2 : List PowStep := [
  (6, 729),
  (0, 123130102197216207287808519720013922773),
  (1, 246048035617008633652083896177212152321),
  (13, 235422346283322084309147431076267348284),
  (4, 178361913330335418956323358048127994496),
  (10, 254673168503053577592844845231048303235),
  (5, 109540148504263335668106606537475791969),
  (9, 104668474938076035548692694822796540935),
  (6, 140108671371876971559015356683715962168),
  (9, 48861729091616861025847255440654422928),
  (15, 60216427737461110616208927389878744969),
  (3, 139043126595594278979424702796489966910),
  (2, 80634808963327930307784251701806390572),
  (2, 156760711265408222659570370465013036992),
  (0, 96095462142211338703669824214879401097),
  (12, 218742996331785033898976045024549699276),
  (13, 227461152913634552425823915971009466350),
  (0, 42632965022892213686680161139596327198),
  (2, 168251798675798307685255925759149788708),
  (14, 205807422651320376743827173625820492636),
  (6, 101628834478036869834831570812078022684),
  (12, 194007919637473851381918663028271736112),
  (6, 114053369928188682526563914145477113439),
  (6, 41348078307886331510862273136867796285),
  (5, 43201002622003947436068742249123677138),
  (15, 26724637434687829285599701055312467227),
  (12, 121446857804833128931408833524225169786),
  (12, 205356494439687225017952822743821726854),
  (3, 105561014176037060989916603505888989139),
  (8, 28256641779209338099905457817333922619),
  (3, 146999310961886128783064962804664894726),
  (4, 255515944373312847190720520512484175976)]

private theorem power_255515944373312847190720520512484175977_2 : (3 : ZMod 255515944373312847190720520512484175977) ^ 127757972186656423595360260256242087988 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 127757972186656423595360260256242087988 255515944373312847190720520512484175976 trace_255515944373312847190720520512484175977_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_7 : List PowStep := [
  (1, 3),
  (11, 7625597484987),
  (7, 4845641173858208981303588456600984039),
  (6, 73292792306749839673248584775711505847),
  (1, 195186755587972429638669896948886001942),
  (5, 132025179597164539486634529497585699695),
  (3, 37845723019685673905843676388933324202),
  (14, 39662062396924219385363015908962547924),
  (1, 203273130594152973424108321310195368446),
  (14, 24215754788207798628852377002944967365),
  (4, 105649925096553857529316796265667945898),
  (5, 12476982100662414043318555750540371995),
  (7, 197793494409371442497971975543825109096),
  (7, 90583937837938967249043209983404261060),
  (7, 196697251285585428606888847857292454070),
  (1, 150227368828962530674203061877715296405),
  (6, 104842294612564388703089457740528319855),
  (0, 179989331836665875170926827233613262249),
  (0, 228634349166763129331261511137997013519),
  (13, 92150802437424977914113850292890937614),
  (4, 87858737435158589214827140010646435950),
  (3, 42001719823637913654813646550408367248),
  (8, 245298103005745255350514497246349376699),
  (10, 17902903159842485235115497821388700968),
  (15, 105175028102046942799221018958597310445),
  (6, 188191210744115465647936622739429607019),
  (12, 223969604700955572049427246538407891643),
  (12, 23933510089393192090293125949796216064),
  (10, 26921953298773925060313602303410467966),
  (2, 200958129684752840360037765230776825023),
  (5, 17053801444516472907913130156215710866),
  (8, 101630464857884484146913207008716355375)]

private theorem power_255515944373312847190720520512484175977_7 : (3 : ZMod 255515944373312847190720520512484175977) ^ 36502277767616121027245788644640596568 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 36502277767616121027245788644640596568 101630464857884484146913207008716355375 trace_255515944373312847190720520512484175977_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_11 : List PowStep := [
  (1, 3),
  (1, 129140163),
  (7, 143267546414143949490804310242153993175),
  (9, 225218831180700642334570063177809480306),
  (11, 51464210226598468211614610062552212904),
  (0, 130955223750130061263342747487719660141),
  (6, 70854831337563838501847187917930273065),
  (13, 40152303812380616043153914210605583883),
  (5, 9449584028008266400676694430432210284),
  (9, 21458914792624761037464476858328622765),
  (1, 149818083576111466423878646643196742356),
  (4, 88871268894082093462740293169130483164),
  (14, 250637468069668442648062533663445811777),
  (14, 80350388832484857334179510960365141607),
  (14, 87342983048797826480388919568668763411),
  (11, 149765905716947371269638991567527886354),
  (0, 13205429489350041986728654592338232896),
  (14, 44404011885359886987231967881489132178),
  (9, 242826198850356905445650708516285713369),
  (4, 38354031823940309638116613816938108664),
  (1, 171968629278511010084664196279601802956),
  (3, 141981365790062334133609201702593893439),
  (11, 206383838713408023098661839544499480847),
  (5, 72504801794363886868090559745168166889),
  (8, 20343265778185648030244238872354325350),
  (5, 203352086939046347659437317253532064802),
  (12, 34016586900708866047880386675949353778),
  (8, 232377574226114210749501055602828051165),
  (0, 93862109180456454942988802171567516365),
  (10, 88087226645677100991424077997363219361),
  (3, 95912233088830986994760052686991751436),
  (8, 216514664320154426008163201710470464886)]

private theorem power_255515944373312847190720520512484175977_11 : (3 : ZMod 255515944373312847190720520512484175977) ^ 23228722215755713380974592773862197816 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 23228722215755713380974592773862197816 216514664320154426008163201710470464886 trace_255515944373312847190720520512484175977_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_1627 : List PowStep := [
  (1, 3),
  (14, 205891132094649),
  (3, 57955345620766859411167000941235486304),
  (15, 19359379633528369528725575253835547879),
  (0, 254658539395915765119514328978243724176),
  (7, 188183821448428633014437518075360918693),
  (8, 75959849440278072591661828786398518610),
  (1, 167627365131998469157682346917513861788),
  (4, 44756048712583544000622883431768223670),
  (15, 19659324040933181616276953809959916675),
  (7, 122389819866119982340684101872830682186),
  (1, 190101247881255382290031939960390035313),
  (7, 110644877214720261496594575497704385667),
  (12, 190000324180228659226073046123243171692),
  (12, 103285009736848048890931513036125164665),
  (10, 131958414809823259000804240563533099837),
  (4, 125262871436805327327628503700007087190),
  (9, 106363461679807684124085020359302254686),
  (6, 176203428683770891481564309134776638343),
  (1, 134356770580657868268841753879165026631),
  (3, 117722291286816753179878579408825566052),
  (7, 74230025267585614899646479936666532453),
  (0, 28023684062784549346895248241503392871),
  (10, 102503152494219508859174692706443618201),
  (0, 210985056829486746029544343253506611357),
  (7, 234874681424468817254419628602483902733),
  (12, 239128296321164223097351050927014161474),
  (13, 112046360734059787017300978497197958846),
  (11, 58008136603106525290541916458961011029),
  (8, 72473583126275438393254198129422586513)]

private theorem power_255515944373312847190720520512484175977_1627 : (3 : ZMod 255515944373312847190720520512484175977) ^ 157047292177819820031174259688066488 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 157047292177819820031174259688066488 72473583126275438393254198129422586513 trace_255515944373312847190720520512484175977_1627
    (by decide) (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_2657 : List PowStep := [
  (1, 3),
  (2, 387420489),
  (8, 71136388545679596084587669372698973143),
  (5, 244887398105590529583902403586859247586),
  (6, 126216661329192772138506632611944174777),
  (7, 229296430754076284504312689046544258180),
  (4, 242426530527404452848646358620424458165),
  (1, 226674610447959303517359647647038218976),
  (14, 251765444595372396497710946524881269604),
  (2, 149867778060998663937956945390106361709),
  (14, 124008145059026598741761357704771123203),
  (4, 1152478917548023435005064925593835466),
  (9, 218745949498419204202892417514462495200),
  (0, 238273023183276165393657817119891205231),
  (14, 1581588909689023450598986883531441447),
  (11, 75868852506265938769365201626616191849),
  (3, 124211729094680522064071274219015916775),
  (15, 165065346327902268772553016125909273507),
  (11, 244403398943971554720336836430126166641),
  (8, 232681515982224579914776429040040946469),
  (12, 37132202257804220298141521241124095157),
  (8, 68291011698312259260535293493514122109),
  (7, 162950973657685924073151891650436664462),
  (11, 72752822873490279950608393790873236325),
  (12, 185924624608941493085521205628093751765),
  (8, 42567541169692003059159829570814663066),
  (13, 19531693133864424905030342034479036050),
  (9, 30865764396974730145059518774572968622),
  (6, 84956755105790666776303016713006327548),
  (8, 25264823290665569537380285172105507303)]

private theorem power_255515944373312847190720520512484175977_2657 : (3 : ZMod 255515944373312847190720520512484175977) ^ 96167084822473785167753300907972968 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 96167084822473785167753300907972968 25264823290665569537380285172105507303 trace_255515944373312847190720520512484175977_2657
    (by decide) (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_4423 : List PowStep := [
  (11, 177147),
  (2, 243745045874792512840565845828404725027),
  (0, 233841367592727282928903190510361051364),
  (4, 207399044189591078132644054004739398033),
  (5, 168336184313166248779604755927387862960),
  (11, 239360231336918546360226316056360980658),
  (10, 135066328252390625994016936061248459334),
  (2, 131376100589371391783514266024509848251),
  (1, 111273873291996966999043908473466202896),
  (3, 86027070396385005289021179990306881279),
  (7, 216696238815653728322583850645589431188),
  (8, 222886979069699775007486498614704628657),
  (5, 42302543947226047576518891849537245363),
  (8, 114702525632665448981567479170188849662),
  (8, 35486210052936540845938050559108005325),
  (8, 42348622525730463037149183356407484502),
  (3, 23818525995890302290679810907403761877),
  (15, 46610528259489363312961835368890730865),
  (12, 145493320440726435308010614764729506576),
  (5, 68793301207714672720027141132841694658),
  (8, 145550775371001467070065455001852650267),
  (4, 19293873669650658276840226537456702548),
  (1, 183796743109119789435443212501741494412),
  (1, 114525420261760516961396481416507981705),
  (9, 235146142048937381239004556657083536820),
  (8, 46229676759709934124452864935095907695),
  (0, 25917393779361008484205599389104451140),
  (5, 119133138062425980259917048995711959418),
  (8, 83399280779944061005050044694706920693)]

private theorem power_255515944373312847190720520512484175977_4423 : (3 : ZMod 255515944373312847190720520512484175977) ^ 57769826898782013834664372713652312 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 57769826898782013834664372713652312 83399280779944061005050044694706920693 trace_255515944373312847190720520512484175977_4423
    (by decide) (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_41201 : List PowStep := [
  (1, 3),
  (3, 1162261467),
  (1, 205676523230399974981364374933088195686),
  (12, 110722995602429809805018173954858908847),
  (4, 68024114841666805216235697144004393990),
  (5, 14998982132137433128311143433626215067),
  (14, 231959704928373508651950586553380412132),
  (2, 245295520007832987286964386422630175045),
  (3, 116032129950690234461740091036499525093),
  (8, 95867764095361219059804271808839071325),
  (7, 135809892096065963269976818756438084666),
  (2, 186427209922576689961250471573898495734),
  (0, 71677463521095788289219679003656727568),
  (1, 30891190528057873611975270858677455982),
  (7, 168698187083401286962052535721834188899),
  (13, 223269041049903404716583516172834942202),
  (1, 247557920604833730734743315355089168799),
  (14, 134070086890639692003821729467301647898),
  (12, 254285193571081772149934625042347084396),
  (6, 42510516958846371604352877873322417006),
  (2, 127316968272788729549260023572758161784),
  (1, 1454203753043404927832956425198122435),
  (10, 108376261896242976481795124339744360636),
  (4, 52138911462320878180278724278905628113),
  (15, 128499555385287253934117784667242349867),
  (15, 71584352212279634655271319595933158724),
  (6, 247823771299055588232425981913779017651),
  (14, 228170497009126585142221373088252940221),
  (8, 172827330636526207461984371528411705589)]

private theorem power_255515944373312847190720520512484175977_41201 : (3 : ZMod 255515944373312847190720520512484175977) ^ 6201692783507993669831327407404776 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 6201692783507993669831327407404776 172827330636526207461984371528411705589 trace_255515944373312847190720520512484175977_41201
    (by decide) (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_96557 : List PowStep := [
  (8, 6561),
  (2, 147747886339628384496645154530509951526),
  (7, 182812741732553954250691638379354702890),
  (8, 186706609074303374830467251997138107473),
  (10, 42470360249956081270612481541906322318),
  (1, 20772901826785854376691913851433438920),
  (4, 27346934567436723284804881115108660076),
  (4, 152088857454699453423169168660694603553),
  (14, 86286265363237147844207217545311416801),
  (8, 217284568754226567037191902715755366553),
  (12, 206655415982812033546339126277787111921),
  (4, 232651411466325960951707495442640029359),
  (7, 2880386656369854787963418777769038902),
  (11, 208374601883746133586468970404920419320),
  (4, 193420322377320298493911111443823970507),
  (9, 73858397025254380961184009311720974406),
  (15, 7465720010641690024659257180114901968),
  (12, 220825344472849965280227093517390725214),
  (2, 49085561227719681025734115858267410458),
  (11, 167555144452243676042434842481318728858),
  (2, 102255323745026307346142929729367007965),
  (2, 194399107588435717756550280514075171676),
  (1, 95306532044857528868213937213390629321),
  (9, 67495376929893078464091530979220169074),
  (10, 224740664822495134662203595092314276196),
  (3, 223979638078612030417041529999376744617),
  (0, 166883083468778870117394356395399533565),
  (8, 255259905881023646761568249610326048823)]

private theorem power_255515944373312847190720520512484175977_96557 : (3 : ZMod 255515944373312847190720520512484175977) ^ 2646270538369179315748423423599368 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 2646270538369179315748423423599368 255259905881023646761568249610326048823 trace_255515944373312847190720520512484175977_96557
    (by decide) (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_7240687 : List PowStep := [
  (1, 3),
  (11, 7625597484987),
  (13, 210765138889567333890949218199823076730),
  (6, 130440984520645752942883318058497258564),
  (8, 165853389357259416041792265815201159788),
  (9, 33016503418440221416033991298230547323),
  (13, 63854853623547002814431239002933518608),
  (5, 190582241847880679414711978639688611389),
  (5, 33078256118435125519313415835776183238),
  (1, 207107445646164791332929323272822586761),
  (9, 120079732086502327501727386586573564716),
  (14, 100749876378094618601302588388466014324),
  (4, 87140426783803353302622240250061732638),
  (15, 94553362058496978793979805951484335201),
  (1, 176743616381784743670994706412683959484),
  (13, 142654253160326027845332837378340200880),
  (12, 72021389947403254628997824639569506507),
  (5, 71730132884916052228666105197091683442),
  (7, 83205300877675365471275380791668523837),
  (11, 86592804594591023687280150085522341522),
  (10, 84672885388900349089044621869355867348),
  (2, 154040702576816423688698035236179213732),
  (6, 65779513535275502376535988140924478515),
  (4, 248434497567931381748261546622218839848),
  (14, 9613318775850408283495113615992889222),
  (1, 165013026585206252803083518930294273146),
  (8, 31043399383638056505926561103262574803)]

private theorem power_255515944373312847190720520512484175977_7240687 : (3 : ZMod 255515944373312847190720520512484175977) ^ 35288908963101546467996824129048 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 35288908963101546467996824129048 31043399383638056505926561103262574803 trace_255515944373312847190720520512484175977_7240687
    (by decide) (by decide) (by decide) (by decide)

private def trace_255515944373312847190720520512484175977_107590001 : List PowStep := [
  (1, 3),
  (13, 68630377364883),
  (15, 130050729196624612274453189406828230881),
  (9, 214516029575803012516406598920413286771),
  (11, 186170657353147614466031728487040573545),
  (10, 201554475019768427829716872311422607776),
  (11, 57546126072095091327523893465366966011),
  (4, 73627425296147001171068364431545203094),
  (4, 155116231157652657652716153876147755607),
  (3, 27605884793165403207989982556027841316),
  (0, 169532912324510902029829615064273238389),
  (14, 154291428690776979657191647357962982879),
  (13, 54916590547201032199124944296072108239),
  (15, 106910513126203740977067725692124706598),
  (4, 118956642777865704637647728110777971150),
  (5, 250783822240309809151975456956312842791),
  (15, 207246647175830399512535317586243746334),
  (15, 229201580612744439185046468645059723211),
  (2, 61211434772714277219728224191226046979),
  (0, 244349465612447726550541857284991917685),
  (13, 111947890491557436393526317703683928780),
  (8, 38072652783191316326059839090492305120),
  (12, 211168284785611309759626840121425728056),
  (2, 31620982279621319674876404129665742196),
  (14, 178697580940215890704278546954246703745),
  (8, 18335160587089267704563076742628378053)]

private theorem power_255515944373312847190720520512484175977_107590001 : (3 : ZMod 255515944373312847190720520512484175977) ^ 2374904191824599455024826335976 ≠ 1 :=
  trace_power_ne_one 255515944373312847190720520512484175977 3 2374904191824599455024826335976 18335160587089267704563076742628378053 trace_255515944373312847190720520512484175977_107590001
    (by decide) (by decide) (by decide) (by decide)

theorem prime_255515944373312847190720520512484175977 : Nat.Prime 255515944373312847190720520512484175977 := by
  let factors : List Nat := [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001]
  have hf : factors.prod = 255515944373312847190720520512484175977 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_1627, (List.forall_mem_cons.mpr ⟨prime_2657, (List.forall_mem_cons.mpr ⟨prime_4423, (List.forall_mem_cons.mpr ⟨prime_41201, (List.forall_mem_cons.mpr ⟨prime_96557, (List.forall_mem_cons.mpr ⟨prime_7240687, (List.forall_mem_cons.mpr ⟨prime_107590001, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 2) ≠ 1 from power_255515944373312847190720520512484175977_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 2) ≠ 1 from power_255515944373312847190720520512484175977_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 2) ≠ 1 from power_255515944373312847190720520512484175977_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 7) ≠ 1 from power_255515944373312847190720520512484175977_7), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 7) ≠ 1 from power_255515944373312847190720520512484175977_7), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 11) ≠ 1 from power_255515944373312847190720520512484175977_11), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 1627) ≠ 1 from power_255515944373312847190720520512484175977_1627), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 2657) ≠ 1 from power_255515944373312847190720520512484175977_2657), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 4423) ≠ 1 from power_255515944373312847190720520512484175977_4423), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 41201) ≠ 1 from power_255515944373312847190720520512484175977_41201), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 96557) ≠ 1 from power_255515944373312847190720520512484175977_96557), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 7240687) ≠ 1 from power_255515944373312847190720520512484175977_7240687), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 255515944373312847190720520512484175977) ^ ((255515944373312847190720520512484175977 - 1) / 107590001) ≠ 1 from power_255515944373312847190720520512484175977_107590001), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 255515944373312847190720520512484175977 (3 : ZMod 255515944373312847190720520512484175977) power_255515944373312847190720520512484175977_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_205115282021455665897114700593932402728804164701536103180137503955397371_full : List PowStep := [
  (1, 10),
  (13, 100000000000000000000000000000),
  (11, 106734912309692684294007676000745115457859653174236868207273571640763281),
  (8, 6709142846424936811509875018360782318219882847211913598497350020348235),
  (2, 153705600244561651635777792925764014225821930902582292170812993003883468),
  (6, 190516976174204569934206414208175050871018622963867881352293730389952900),
  (0, 18943023072526118476639798631256564140632079598689270117398456299595524),
  (14, 162529337301740404350413544812550483020864513602662591077104314219182615),
  (5, 204025578117192119820686338704657504693437645154959668437018725831413051),
  (14, 172193284752466796845243604656319898435839583998415514550057919377003070),
  (3, 180357622199426266028136708215792554584769440688176278914386714181512333),
  (11, 42638091482373340326981324128864836153812183318849662486977909115269542),
  (4, 203305025405491633142559440648274787190885880568756009186425521894856706),
  (6, 124058979057081630796546246637636506958897465181868616072457961107056462),
  (0, 112228197674104574712995056717535159753005986818995220539255590002380068),
  (10, 126759815221525089369894074758267711947065884337346795444939868184455509),
  (4, 105054970435004858916888404925818867360207829160308347319494687537223865),
  (6, 97937762073837907308521980571314401114424205885068253890175740489068106),
  (10, 85647019273980321714652993779759768917724193894884163644548051459083524),
  (0, 111229402301580545106651955056462415776585786406890679448604340687995633),
  (0, 126159719346306695137720478317129142323009517501863660345679754727871979),
  (8, 173923775335778858255087195006986184460270248615442732963341690977743409),
  (8, 42578743610870106042130117910612381480464735447740330817519063163401673),
  (15, 34459351767608744015423586021020845283497103014564730928820544919242002),
  (12, 82518582123118661117240347562701340015861560991404089628996595362848484),
  (12, 14368432792200403204957162719475534704665546404860275091290781831177590),
  (15, 162321483197371186550766811375161085613026176600336694942038825077077684),
  (6, 160634084451061065765783564532127839399766957303180938906400378205238481),
  (10, 195912083791681562014970275507873654846034829183011553009507755268118334),
  (3, 35317612550338304873649452629641545734874685385473989614395996950978604),
  (10, 192798016473563838591034729251461576421497545536061941564707074169968906),
  (5, 124013527234304413488242674662095288319728732503733668628107184036836972),
  (9, 14735577535784772941669290776772392647082377603361180592887714092457686),
  (3, 108146375300934314557716007976085810807445865567630096331703924982812633),
  (6, 166602354262281303490824906254003477914576293872562749716738886949170982),
  (13, 149687535743111439722875284764038474977814979657100807654215063363575163),
  (7, 168711272451121675176819953048093772927610332085966866643071213608967931),
  (5, 80268231522288737317800736144800549084397111902580195825245634661521181),
  (13, 48185947502023522505042189118520125363756025674785182635319808285511515),
  (8, 69202914473075195460194408256723078837030878604645293317203825845446990),
  (9, 185480574553791485189583732984111895996660448374989826218494902392142612),
  (10, 113814991984823674849292278395618107852099219261959337411119795036027043),
  (7, 175142446514064262342641667219635145554837542633733281453486063564624041),
  (7, 64892660389102919032360560752077109364743523100815337000028483305851249),
  (6, 80709240793379032101166861667315108587572911228331246212868720811963031),
  (13, 124727870171272159606271862982408069096079254054158036894248040339944219),
  (4, 15690317882142580384012272832279508864884607374531439813627314365879252),
  (12, 198980371137990637499473539504890075917486153181103816337140107738825911),
  (0, 151330312972308877806738021574948685307690097330761587393154118470961829),
  (13, 190739541508794178741130905904226128969839606823750535277527844057995403),
  (10, 4444383678771799173252873475960421453873858618621008400393307625421281),
  (4, 67495347382768274012022882625930068244018714717214040263257486966548349),
  (15, 32886410580834370713218797311898211216560937337610440083819372301849486),
  (3, 62464234368904642286181882979759356675405110740824337853289480738096934),
  (3, 43698337464167170669532080383463984453140941758773918984484846421295832),
  (8, 202090102619967959943792666339507436287716175847149979374997054108406526),
  (10, 149117041527850106998345012668520885447850982699166453752216466388189635),
  (10, 43374721378697035570117318471538406664214620505176113330912205585987360),
  (15, 204648792851295097449293354823303120546160439127147518499545215557646873),
  (10, 1)]

private theorem power_205115282021455665897114700593932402728804164701536103180137503955397371_full : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ 205115282021455665897114700593932402728804164701536103180137503955397370 = 1 :=
  trace_power 205115282021455665897114700593932402728804164701536103180137503955397371 10 205115282021455665897114700593932402728804164701536103180137503955397370 1 trace_205115282021455665897114700593932402728804164701536103180137503955397371_full
    (by decide) (by decide) (by decide)

private def trace_205115282021455665897114700593932402728804164701536103180137503955397371_2 : List PowStep := [
  (14, 100000000000000),
  (13, 98050218844089758437534783045146513542333466779625231270204193385834010),
  (12, 67215330545053355740955458102018692855627318322599146752679400003626493),
  (1, 192556905286441372500811132022844348533021972412083834112226148505634403),
  (3, 28280777584836502884951076906899805956054880517195433955462305187372080),
  (0, 179176058734562140003011497558287426222039245845971322406873946692625133),
  (7, 22337015347529411069282622398143012931991732645044404964357933008287825),
  (2, 59871110645196612176712274689677357665983506885851390973734353771290809),
  (15, 8509849072203147133704970730071230067393653895624158666900112072997801),
  (1, 152196289160140961912629447597463936426370646737192710245964444230483843),
  (13, 134690746240274408887388787474501003879505273933738373914791257906704332),
  (10, 191007405779495481345495331594086067724515424843395436822646680295487206),
  (3, 22774041786391996458156669020368524066311574383204664227880904302601314),
  (0, 120646054759058030640304802721626965065537096402623629170355662809243215),
  (5, 49248794374659950972934017828696995953454681934396266290033447741604210),
  (2, 15980660069744278363530663937472838550959399622393807262247361496224962),
  (3, 37529484090593680863404066119589756851278801077816081884093104929323405),
  (5, 4753704174765748303104000214883193804954460406566865270739991403235121),
  (0, 134561204523397185773713414980196608819539907647914092629416007998281359),
  (0, 113996113476172011481765433109330406475594732917089429511117733466996391),
  (4, 164624476497990022763112415649316438245384144927042667774324770969818941),
  (4, 185340213469960028516034308597004731675208100811273431690502133388857386),
  (7, 106482716739941305414507247677819874378475705067994919335198367026623690),
  (14, 1456530324046570965142388537947518133993506139806926537260192544928639),
  (6, 84713681227580449725732571543770631195242188225410591263134419838050264),
  (7, 105807394168422060698087849461607121752253567472579334737866447084028471),
  (11, 105159867749515576952046162546428167067958191335190324572726341855652560),
  (5, 46546813537864009577082768182142675961588876635100509342526796188288506),
  (1, 137094254071041409067576257116484314622238955519193160456636429939109852),
  (13, 85231555930974178722950936478201032907995486183677535468913579999720464),
  (2, 53941581282420516965436674513881145470153758011826736259334299688880887),
  (12, 76649812875413796202782143116786225567007668713848700145255687337535685),
  (9, 48824741319028935502930194482950692211882713508094565608933622262017409),
  (11, 10659151638306276883767215055975280594917669646631677356709313064334872),
  (6, 46005888251080296584166125845217986550151590343111039719664379485855237),
  (11, 176261691597511668808421740010041922733951783355325099451027911459559357),
  (10, 103123206764903915889527829947329915445780953218765793876160684960708865),
  (14, 204691772833171727446749518512952766885773838717637239236993447832243771),
  (12, 121941447820132259025243881822730881650985381577547260597125448799290822),
  (4, 3051006228944355514536510620878889612712735995158039781891237535136651),
  (13, 18377276853693815505307364814637482193644353135461130298904629319453740),
  (3, 169331083694116842872289357264651847166128550683047008513356214246361926),
  (11, 61518237258741847231883582784498800485911386052716740226252645666252106),
  (11, 150967330499701418183952847723466910384162291941804163844028965997587377),
  (6, 156894353484063468832072892109927324183227292469666902125490849128737921),
  (10, 65320512004489323283828611398780948354972134396855013026834996068411380),
  (6, 177213660267548510530907113202640988925000882632840121341770970117953601),
  (0, 70386338051231711838976684798136873336923113779702627237962992860312690),
  (6, 188161272291462478340483551587126412041628567323965262395813441593297420),
  (13, 170421852609104366014858188642715688880783810614138181387913060062456649),
  (2, 174710012674542220243093334383153920725048802449754536058296524642921551),
  (7, 151358468054784707581487862269573041747441220542578341766929738490319875),
  (9, 152700134137007770865929562689997164917285626235071706935259504467414225),
  (9, 118328817684342725313737295797682613092925082191817581182799049338978764),
  (12, 55432893862610660734375108892174655417903880179388582786621271304852401),
  (5, 5366503012067304258789470338308073894766082776165158560281682052561055),
  (5, 8086585477736310995102411749293770909655888454922527927550137658910517),
  (7, 38965788090594080594866867091555926484443509390410006310390521619288235),
  (13, 205115282021455665897114700593932402728804164701536103180137503955397370)]

private theorem power_205115282021455665897114700593932402728804164701536103180137503955397371_2 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ 102557641010727832948557350296966201364402082350768051590068751977698685 ≠ 1 :=
  trace_power_ne_one 205115282021455665897114700593932402728804164701536103180137503955397371 10 102557641010727832948557350296966201364402082350768051590068751977698685 205115282021455665897114700593932402728804164701536103180137503955397370 trace_205115282021455665897114700593932402728804164701536103180137503955397371_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_205115282021455665897114700593932402728804164701536103180137503955397371_3 : List PowStep := [
  (9, 1000000000),
  (14, 4747000719602401491799498907998409033368222291470148214345156873332729),
  (8, 196692075285628494056718670844750636442573627036402745348342464984873133),
  (0, 204967759518698116404051608274391422002163384980848732597523637757667388),
  (12, 79929072528635402339096466496175482040622964863872790053911335363597432),
  (10, 39642644432328370124705861513433514776090984885743699958178478854072644),
  (15, 158147696141397884685656816908473472310375762843316077950148930671554144),
  (7, 20378316995100814603330029040481192214609912514950519952363436307478558),
  (4, 105299124848764567476804552473669985379526717566867017856975954035751068),
  (11, 111386155598484026914473291832156234271504022954879965048567766270542578),
  (14, 29538027774116783184040599351386418178605764714467155539134996828190911),
  (6, 140558619168582121334031782623078866707523700349934237287022387871561085),
  (12, 18535115007204233783484146556012799515801962113712853458527448375315975),
  (10, 204403434145894961639506292150334774740005315264563130980941732616532652),
  (14, 126795308418733304035206311151455420272286657153365623667263290198522443),
  (1, 146427238600164271664965455328967060444890804063695389920599278703568304),
  (7, 157805934548264691121739609945492469560921837946616137990926417834139150),
  (8, 156750745903083849702880979979300080915570247613240124797002063466091968),
  (10, 200023382739821411479876524193653692151146779218799954889863108603876020),
  (10, 136250564464034939441037097051507211889113677566805121495359256702898744),
  (13, 148773740589860748097084269214519116634281984642858178581934283320307566),
  (8, 116295000445153458577982945306947853658221379306947847126475399927647417),
  (5, 67920376221748228498745369812997880711582956949502929747476891277674710),
  (4, 131768808189994607799659655652691277534465388740264006148399430724684600),
  (4, 108160339237790996940651369066366093801504024207340054390877946118130889),
  (5, 182567536742322468833217863938748240157297940783178183509474122340463107),
  (2, 4077452594372502920674754255892021639067739880310032012032897474279568),
  (3, 167713117783976908488810484850561426433830013310620472979647043462303975),
  (6, 103613463107635723602218905902379770856337936281953447330642200108344669),
  (8, 70471675530223269678420336373756267322752872153828901942505411000072119),
  (12, 38341477112658367176297332278180712148123631616700906144127852946761844),
  (8, 9896029653695421135279331156299539415760296668308498756064574379530336),
  (6, 97394117783244194807631057126017718229650239244747769394177734440134047),
  (7, 118813912431154194133135403082456364483434649575334839221353793723584467),
  (9, 34575221187489794586775922442807964148470562298070229444861126511455907),
  (13, 937378461702345515219280597018850565906374026045387497910365626667881),
  (1, 35928749376874279815981881482805763547701156720202974200560882946242249),
  (15, 193498973284764692700091391377449263706121184121468857318054758261530705),
  (2, 78272568769135025338802615522793715392632275407262695877103655592099068),
  (13, 189934673232553852612810570496270477780641821329086135464334088266021135),
  (14, 150409905307516248912959551025761462206208025593447108214823532467197775),
  (2, 166166043492331001887912016723571620937865366105693363893053360571291906),
  (7, 127516863980762939447708486865825934242164516675804622874459154787745895),
  (12, 118167910856856047116565317951730959656277599575696186967851753621526093),
  (15, 149538422508162463750249253145849133781309192175910251570514100934080811),
  (1, 37217337122858136709225526453501353380301258097709618111826212150662473),
  (9, 109771624764501009563243275249495281717839851798898287769757693722418816),
  (5, 15165723853320822981465646878989755555230377031868493456192438623618835),
  (9, 20923785566434951369228928620940393122502115622509845135079504049213448),
  (14, 108178876576230517781442466379337837453801405401099160337113655216394373),
  (1, 54150278512764761287109749281931225307522873916117927377257560885237546),
  (10, 112326443904821179541122518185240864142224811520716411025199560018583379),
  (6, 128368065702363702989627971189950070589008394085333572655149024872062749),
  (6, 48526706224215342693155850401093093396532483341095491919787039008566009),
  (8, 154696882432781355240989823686920538235908154030374677244514799336489711),
  (3, 109439031285537897814686329718823592149112001617113766412492006114538494),
  (8, 54698760945594146256939205822894792510004499395964164376972718642091889),
  (15, 154439871705787419141979173883912623589358086515179591858437065999915284),
  (14, 178616112238072933217230078226700686412819640559154366246118991325153614)]

private theorem power_205115282021455665897114700593932402728804164701536103180137503955397371_3 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ 68371760673818555299038233531310800909601388233845367726712501318465790 ≠ 1 :=
  trace_power_ne_one 205115282021455665897114700593932402728804164701536103180137503955397371 10 68371760673818555299038233531310800909601388233845367726712501318465790 178616112238072933217230078226700686412819640559154366246118991325153614 trace_205115282021455665897114700593932402728804164701536103180137503955397371_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_205115282021455665897114700593932402728804164701536103180137503955397371_5 : List PowStep := [
  (5, 100000),
  (15, 84636550772981666533710648947614931827195772676987327794947416571766815),
  (1, 199533779629495434916281984061138916534009689329028464457560527344652801),
  (10, 123936460911779807111934651033640650768269212844988365639946742646588664),
  (1, 169711872427633911901584506982196280907042983345402895914577866986369675),
  (3, 56975602953198068907775116957416803854599744112396798940871131439791056),
  (6, 193848641862120297776281210708308321776917701393313785983749800071078132),
  (1, 72429650354630778290881840354106448581355730034367927766519815794520736),
  (2, 65765485222292580937762338594810489378520368329887026363706457596941099),
  (13, 200913426364938023986230501289820774571938143414580125061443682876886230),
  (8, 169870775513803151497129214792086709720244084795762713138101154169749173),
  (10, 196367451839599167801046438601416350985204428116094071111703394956977303),
  (7, 7268782380311336589284722778217407743863676805276210592274591344810442),
  (9, 182210897887946498037435934045444072043967424595389379366652661695760813),
  (11, 105972527719337200905680377422941619879196164015840379549548540973355174),
  (10, 183326835575595860429827014606970724131990276028667207062753166910409699),
  (7, 125830748679305163821640971327154985962745387031118238811199659029712194),
  (11, 201682345464143638424349342205693984476567573447095340343955134085644838),
  (9, 126573740794049036979708974269443968492871339070840883769668691771636740),
  (9, 6071600925288485083183251742830879604579205235650998936822718281267851),
  (11, 167504454723480748454613190809634765841083383538472522950351871499729643),
  (4, 2579079780616531289836434156516517835889882527637920822800045143610422),
  (15, 40344666375106398267002341182834742553427577863620170965167640444266739),
  (15, 107352986542881570392615552486644068653537567385480578169445637737889478),
  (5, 166266575776490581090269793280821339260152372097816711868992476263468965),
  (12, 122816944853970128883607405336218597728798515419558049219020936193375920),
  (10, 20355322571815993289656309118674129897095296603545205060179539442066030),
  (14, 110257167195527449576613458807319313479350713113150270652151539157137815),
  (13, 175977890694532642478570598864077804242784127959344393134196836469072835),
  (8, 104180469188790194743902326007255533525283535629521714424745390025575679),
  (7, 71164840283149888985125602429855188728797401721728675898526673555275715),
  (8, 50615871433369686341345676649956830710963762425439672368892650894965103),
  (3, 145298253139648401637242502758304058450845336459648986890727264416474215),
  (14, 65644807755731156154867984305730817126145407659881089248349567994496194),
  (2, 76383109874937058740066425828558943516917142333250964148916227307879979),
  (11, 39452222649804268921602092938249673272297909640571869316775623346773943),
  (1, 117279026279009573610601331219695582335927668075483670897885286797148739),
  (2, 135501953894398159379542966294813681415628263610326438387464795704004728),
  (11, 54016554332371386475704412322306692390870092543452010697313229965975159),
  (5, 57943879067794758507355823733905910190710209166185446204502551023847017),
  (2, 20727415689982601642023539078989039225858979965314814687113747290056648),
  (1, 7727130764168333807545884365217526178193113987057339500476236036836336),
  (7, 19810381798544053999110253062046678678618091541425464174204824971002576),
  (14, 94157110449056239455878457137825172328665588310686896003137174991419556),
  (2, 58062030388289389346165938679712458229510384785122043464386988573980396),
  (10, 96374676839004345422815079963299683361485679491988253087919804513576354),
  (8, 166454150515758034806045676854937195507230265863678135677727235375962202),
  (12, 151415041145949607040870753615276535840223408148418631078034434790572364),
  (15, 77155499580204083330696771624747373680890569933677899841350904342110424),
  (8, 164648701546131822753701306690351226431106753043236795260619571209156325),
  (7, 67798068720178850225133059939046328016995265135861676655529196401597485),
  (6, 98189783772467566920895230952325631740412164348238843257845471627914346),
  (3, 130048233193447662223525615914771216287143556006136376009739209381670020),
  (13, 149290168393300425537126272919876852674436865415937148966467000636634289),
  (8, 60374296467346493277319406043359857576468274216583412554112223764298146),
  (2, 140383563133854314432633423275050241702475857132088684021298897943918835),
  (2, 181896870484525501588317274447939076958931996120711129339451933783930134),
  (3, 1089445820471828345341278147668534093783498593520836413114983095485124),
  (2, 148667663605783182964533161827581554934625546150551877457291286907751879)]

private theorem power_205115282021455665897114700593932402728804164701536103180137503955397371_5 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ 41023056404291133179422940118786480545760832940307220636027500791079474 ≠ 1 :=
  trace_power_ne_one 205115282021455665897114700593932402728804164701536103180137503955397371 10 41023056404291133179422940118786480545760832940307220636027500791079474 148667663605783182964533161827581554934625546150551877457291286907751879 trace_205115282021455665897114700593932402728804164701536103180137503955397371_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_205115282021455665897114700593932402728804164701536103180137503955397371_29 : List PowStep := [
  (1, 10),
  (0, 10000000000000000),
  (6, 179080975991265443454876465784454826675158103320336822440499506027621921),
  (5, 56067943789883949356707266668510210758310099681679192078446126013600750),
  (9, 63526651621522262541021513307393978436795897874355861052691257395515470),
  (9, 185449929490237569511462816162558764100861082578177397700970246680817053),
  (6, 93266950073895399230727293558465090601133347931447012615054304127565214),
  (9, 6288997714047463354032828278191563310086831018430349085841476100625617),
  (0, 8241354444433604864222562280606626581487523334196484962684367556577626),
  (7, 197656139029134045625836667313005373323420324425342651011468023886832209),
  (13, 53571319709524439568958183865103351189113587998702285930760199423623724),
  (10, 64440381287729038915586598455722543725514712625343616971376232836940835),
  (1, 26623599105962144237213310519663589440048455272844933212556009691069334),
  (4, 127329764745526824230551099860155327454140051926503227063585689966665855),
  (15, 192869826278636899007076080760041421295741034659762217823144257948390338),
  (12, 98936747077278221091445073294306457620520977907447849102378116758095123),
  (13, 176781254947640206553734117246470758393203273414193220468811837168892104),
  (7, 37342126287204495262451712715726619467064397200979224537534438520412453),
  (8, 75198620417158511896940359556156055510751055862749938915769299414871867),
  (4, 60413095389906417767636065152693675194248587395628227838299437460732242),
  (6, 65932518519083037954360237695901753441532638353086845311973230821056704),
  (14, 104937768481380660501158180283133753517004051689815510207754978771183826),
  (10, 104688841913972074051306470859672196456147450446493322953886667469104377),
  (7, 180641130921793962933667236732034587032319358423061752150737296873248376),
  (9, 145334820119632126368652962980020208143828758066245675830350657469055982),
  (13, 75834007267059124008210368548877963510606827105801187267116898821790439),
  (3, 29602533476757331975147499830169854396036804239135937117462192561727875),
  (8, 135547774560648606056500243867371743671509155435848535375930123841661566),
  (10, 123950358679127318430477039951270021307055644830313193225872227454991048),
  (0, 132427172784402580465577188092820770195918619593271368178835113814921327),
  (14, 185480112992937839005791887695239683622326738321480756424825817789633659),
  (8, 151983920169154309733574984944434437059393809257085735012618521804126179),
  (9, 182394502436931859866677146893962892626040443505691360373341393049371794),
  (7, 183982923197454990368880483341692473589396512569771563266935966205193306),
  (15, 150137972209320613451166177184737800752396648093126066197011931580417502),
  (5, 152822344628181173078804304745913057951767134715500860847739417218419919),
  (12, 28747264156143881887560108280677878529903119116714453784740426842048664),
  (5, 5389301056224613117466793503577500671311636949281405078963332213951400),
  (6, 37523667328730454181007945353941475386768381128303658099768092532054032),
  (14, 44007760936847417986605470279810861061964162409361955570213960978400780),
  (10, 179161107012188505920233815717355790206956918510983243227686286946226844),
  (13, 53589141631895853058246962370916256932965791575068860878970203343624579),
  (7, 83414248000429878146781845931984584145216141941516187618943957319474561),
  (15, 85722370472241190734566616308314280765491049287542554650726751160430445),
  (10, 75445034268340930074994594947968638962369736849980363438401450102478248),
  (15, 71499632056675927659604531091255402647463250869796287714327330168058891),
  (0, 104984732970628681447196149634367004881231827347560423831439766567772189),
  (15, 101830053505726211658901950793922661239783605205139362565768950267056150),
  (7, 62609105560524251274970592246326122100067955575564725427010034528092246),
  (10, 24293241674723826943376714289291186264400440127618278117424103089286978),
  (4, 158744038535052676343377666337200767568625431436731748353115146842498921),
  (9, 195256816124184988858384230776165991797233722474213581912063778931277969),
  (5, 14768358663179618361219352712424184707666086054335806940033698138707154),
  (10, 58103753491929559110708575552639522332582966014837305638753279276251316),
  (0, 132881400266677302213609511648871527659653757428981747357989238863439307),
  (13, 170896982593570978387131798946099137058082319384242723378911388612287777),
  (9, 84278086803690542132939610849399122101349780013893329333872645987013598),
  (12, 85355445555666566017622891881291246081753423756893625809669199125036237),
  (2, 90719238424619861502781386762050866835022444605988461034414193158222234)]

private theorem power_205115282021455665897114700593932402728804164701536103180137503955397371_29 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ 7072940759360540203348782779101117335476005679363313902763362205358530 ≠ 1 :=
  trace_power_ne_one 205115282021455665897114700593932402728804164701536103180137503955397371 10 7072940759360540203348782779101117335476005679363313902763362205358530 90719238424619861502781386762050866835022444605988461034414193158222234 trace_205115282021455665897114700593932402728804164701536103180137503955397371_29
    (by decide) (by decide) (by decide) (by decide)

private def trace_205115282021455665897114700593932402728804164701536103180137503955397371_31 : List PowStep := [
  (15, 1000000000000000),
  (5, 51385315524896314109176101830316504696446496465504618566718045860554097),
  (6, 54133562503870985497856774960077293504120309095950193478643251423382585),
  (12, 125328377705436178376284885656129710928244801500150973118845746600379681),
  (9, 73723394488290211418173811220947590705531358305124408334476537771074603),
  (5, 18579395418916666391415890269769560355951126878737222634044497846294366),
  (1, 25230729896959539802078206103654048072601156762877711543634295434164247),
  (11, 204145162063273974126700974892318412481125022432825355920113296214903038),
  (13, 37267623279927063622882819098412856158005403049631637194837905722265710),
  (0, 107526296412210559524233244050593884605601545216618266557642603071638744),
  (5, 192770701726272153184298428028107605672646675297714770812251680470839915),
  (13, 16456438787382476924632416964034675721622876651134482498923997715900425),
  (1, 123698005730137263733129233074908652608146765502747506825783942820638781),
  (9, 24438938961277481169272473599171989368009337403571130885910060765215207),
  (1, 77323317663153369940980846966537495767328447924769567454586527332415313),
  (11, 171365621361870044957192984604026882858262009003573676085391995884071444),
  (0, 162445408707804314550027326186404775632513944252293926986383812812933990),
  (13, 120586840936940835471235704985787069459310486211924953375268549548998304),
  (6, 85553946064423142682293198629920959334026583388424134324576663744118528),
  (11, 76961509081637500962725543789551060273367362400876855777010913755995351),
  (10, 121747549410103492149598445794007712996476960034120395241522709154419170),
  (1, 124744843032067864485590337505589040538624775902401344023659512589235190),
  (8, 35629103332837527355873494005295413506398653146067787682448882995351833),
  (10, 57525318546124245764698385055272377332225040347971069810408275041955451),
  (11, 100752776359722234228953853924269703240211176079245481503683650266460733),
  (13, 38769297372192088470675186245144490139326054461598276487521857052865839),
  (10, 42885917622143309752120013754169158604858250805901598501818252085930009),
  (2, 49241410205323197774538340106009584187152878960672152018361699085395424),
  (2, 113808424772257382340573663140472067317029298959128611292412647893228020),
  (14, 34646339166817849670411686009384877926941529108587389490560426853609499),
  (10, 59911266393223054119452176360864054560917210089960522081554782305098087),
  (1, 121913912414041921389943291319766566553294656820380721178661452886999024),
  (10, 184985265801940713824437702014001293040772907176854762848521437160654206),
  (8, 98616710044550189138214467070163805947529783732485396046635736556617128),
  (11, 202027520088147322562646238012154993221243234648173922038930320016564874),
  (1, 196410316884735287924940871124027996724134262078631009166021413565625235),
  (3, 20043091004896880521542248875694721841717532579221933166439796719135025),
  (8, 148458403824577819809534017080755614129590040015143219777038486815064842),
  (8, 158349779996379459743879426252073339596743835036038344580700790580290596),
  (9, 193753861694358309660584554797597126051063572927033492614293169957032766),
  (1, 155543267993283513494871636933704967521071127125980706910110260345732419),
  (12, 126800186407248989242216257489642753082239186726669759752925275313320870),
  (10, 177970258801738476132747602659747697207434329866111265742352855585620280),
  (0, 196583762456944113165729690359051678743335681470463379393026327087363217),
  (6, 12525483770142874929461636691366855689461333407276739168774890095702628),
  (13, 198864340421671587004065806567283036811921075471123566822991882736515939),
  (12, 121827304100737418651436742010730311861953001415526848719831834825117324),
  (14, 144735740547839862035346956313696906055805199616599286363457453358399072),
  (14, 129243000461189746051872178891732371294560830414316506221027292421537849),
  (4, 100327117169844083091446461887735592642540600712046725437999051059911510),
  (4, 40775956539205421439890452964309249654487943541968833477108743858381036),
  (9, 31392777377739207813695800478224692034475364273770568791696107031736487),
  (14, 122664997713312888425858269305204683028407586079854569736726379274629437),
  (9, 43202129508590452225986528060351683339462165069832498380220739999634623),
  (0, 191972250294692122895954445804830823712892905166792998493114190777809286),
  (13, 155128087331955003910014065434436882262748766633108558814810799415130261),
  (12, 32952472309088964466605768016065886197747907703363858640616340498493027),
  (6, 178914599646525377090000213924526954283063588893967770896141456545640969)]

private theorem power_205115282021455665897114700593932402728804164701536103180137503955397371_31 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ 6616622000692118254745635503030077507380779506501164618714113030819270 ≠ 1 :=
  trace_power_ne_one 205115282021455665897114700593932402728804164701536103180137503955397371 10 6616622000692118254745635503030077507380779506501164618714113030819270 178914599646525377090000213924526954283063588893967770896141456545640969 trace_205115282021455665897114700593932402728804164701536103180137503955397371_31
    (by decide) (by decide) (by decide) (by decide)

private def trace_205115282021455665897114700593932402728804164701536103180137503955397371_7723 : List PowStep := [
  (15, 1000000000000000),
  (12, 196766350599987302344407550937039889330482240253805228604934015074747139),
  (3, 70514888818203051948196042309664893941932166770163313459673175825513468),
  (1, 82208829809556281026905640528292390673849096670398811601072516105646468),
  (6, 88261388418766837152166404323742534688123457361115848856808941827344086),
  (4, 117907643833513717742767701606771091684637977223039088559131704618758593),
  (5, 9973404879575850926256996114762986964014909424422788748765863801396910),
  (9, 35588089405737363423069042510326668858335939448242387174681697048028143),
  (11, 135929400605579500415863403301433673097466220126550600491413305290009278),
  (4, 68986825727971163592057452831023287069380773700928258547450481464506243),
  (9, 94587258732110242448150604549916827776801528107241241725175408026464107),
  (9, 112645384951789796216594419865489955067543834238312751434416575595132324),
  (1, 60876077657765017912841509699701257573235770329539027769121063025646219),
  (3, 167221947698924704088989657872396567347802595310759901698226040021229674),
  (13, 117517794645891148809257258244136184067075620264752103373243709687698242),
  (13, 131640137541762631167179764742550000258266116724263827217090341164379898),
  (5, 132568887707974814530385052731206954778022739958383943809420492913458530),
  (9, 166992110830476274478306649867868762444769051453477813889522139982536567),
  (2, 115755935736601562023888905264222220645471121417407930069728947613871049),
  (2, 123772937214729798333902863704287894915834081754701792666301773537819139),
  (10, 7399335794798943461592017968734855347427454504273375543920838006297221),
  (8, 203415299104776202248421288764843851163589775390825654630807059830666364),
  (7, 40772341543072797777665260770888353939813544509217486942284163699451048),
  (3, 153135593291285587781535043271992613846735756976968517046791507674346143),
  (4, 291838933352397730226333084085219165319212658737263164013742637845063),
  (0, 64744559121785248415178004188901131358555394099186328912120812095657904),
  (14, 196485498267779365992134270336372162803966449570546065161516122561010898),
  (4, 115149535867710044399308712028935030017366735956598035284663915127898058),
  (2, 171121705132093877871910338259513446119065237183631951525652760333702788),
  (13, 136092129606163120871846286968299221263980504500917979761142721348390696),
  (6, 38222178309273096758235672748655551088955080569548983661122051655493743),
  (5, 53870756972589445049610237291160175804922222844038099974815566958611395),
  (15, 127427279290701566643223630912617885528889596317330765182584808078389199),
  (10, 107516566349044386684913225823649661561227422523009488431748579503070681),
  (0, 139166842198451422994622460963401302882131775378565187498055848239984052),
  (3, 181669089644969136061060723164174161732786385501997034309653053097429429),
  (15, 136504085158813756666866418193259513418543385111867910618851334511652165),
  (8, 83647611757362270443968891686192296363848450203363136508996728136207239),
  (15, 113349281079460911038716064487941903623406897719380531834428960530706147),
  (14, 3006788860224747551936044555691993055974648651648368532761479320709122),
  (2, 138195723963189320706268733841180139828328560484358980953552075004711322),
  (0, 29504103042855223596456853981584340283305561317348633851875781620961502),
  (4, 62232812060977311274769390290249891187782301030429519605148707227514731),
  (4, 61787521462007806365516012460795987167648655907514917420251868068419758),
  (5, 22331689029700378934191927604435773887535777803705667551447169715185366),
  (3, 135868122439584278104362285321954592038100202535482436125567282689291808),
  (12, 73213533269488544326977736327413404384363428574281889014152755592017128),
  (12, 200011894891626256650326035411657177300777306270877740498014749432094938),
  (9, 124745167012229922666288924911911271727366805847263155679464874871109728),
  (11, 172260483596890436204271592499785017733996674356373368003393377611646051),
  (15, 30650441445051496229206581143281015603038681484779605751836148082557524),
  (5, 202157748599615993433017541323125358252926835644088700424629300663117346),
  (5, 18562229907109675439630493918982112744098976039634470085779884592058253),
  (13, 29650566833566780202112346456464977488155574143059182641656622522890759),
  (14, 141143613142701949781691737750982902059573808900421981325954270966026168),
  (14, 123665784261542600597161422878187596862401757469595512553658861111742805)]

private theorem power_205115282021455665897114700593932402728804164701536103180137503955397371_7723 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ 26559016188198325248881872406310035313842310591937861346644762910190 ≠ 1 :=
  trace_power_ne_one 205115282021455665897114700593932402728804164701536103180137503955397371 10 26559016188198325248881872406310035313842310591937861346644762910190 123665784261542600597161422878187596862401757469595512553658861111742805 trace_205115282021455665897114700593932402728804164701536103180137503955397371_7723
    (by decide) (by decide) (by decide) (by decide)

private def trace_205115282021455665897114700593932402728804164701536103180137503955397371_132896956044521568488119 : List PowStep := [
  (1, 10),
  (0, 10000000000000000),
  (14, 36805072310111286387093543670648406213654271752516571799476431060954404),
  (5, 31719565498550446347812118874690585754689680319389169100935021472073326),
  (9, 80307271791259938094305685603184518554334244373629564081770864334982471),
  (2, 179524489917470610758443933655285196026519214915928960631076307563668929),
  (10, 71069180094202545901257144010203603300215121323788062263001206812716426),
  (3, 134935132016215010269247537881070426876152687537404298178642666275547109),
  (9, 151032864674812409781370636813660609338640173864443189738421505723698116),
  (5, 169008938140775171759071727814465894322236414643827778595529199469922166),
  (10, 198786658482118728012242659729588700401132465994902749477394190555793181),
  (13, 168420284324005580233859580339245186742363097947629826504284352230211145),
  (6, 65372126931156142667307481789520071231719950529332919094591982554867553),
  (12, 99969045706354383289585220220124690880736158505376125812530241441333143),
  (11, 23982622381866666107264094988843428885649495549435219303320418636764486),
  (8, 84866852813252320190016802303672207690413309167932742687036362570504660),
  (15, 159815430859920919022509657179725451140289441864435428096143255080995293),
  (15, 158628915927826388303629020399590130410374546243042091765095171681487413),
  (4, 67556800870292590493589346511409667057268798464394872120762305902212562),
  (8, 162972063817195737822694559497465085710004923464497764144679687943595110),
  (13, 118078892338503447671725028391251940273840566748173556682560800161716208),
  (3, 14596614788584780096081584214229439460405276790103733506793061389244871),
  (12, 200756782869833073120326734246610543186728575106473546830527852300450761),
  (15, 31169135254458127928084399339353297977459063696318260052296323429015650),
  (12, 53400932225811724919826660027478223888323723858970376527902907539102378),
  (11, 118738124639646507518162220473839293590850388307343571826466375087194842),
  (5, 175449929305878380215721129698681456504825990004147938091620093683742918),
  (3, 127842367441874244236749781980045301753957555147346565548878766805499764),
  (14, 1794296950571986984982398499679438374247916939585974691012789619699305),
  (10, 30814230330448669096799114869479048131007179647491855101426598149203698),
  (14, 170733566351571868990965046502138319371720194438558358774108044999841941),
  (12, 135234856250768036632490772045866265588999894258431155255725744406364837),
  (0, 123150996370430999497395026424496786222843930727298729168965299731838818),
  (4, 162186677681093192108838909756194547900478146896649118534940770527421569),
  (14, 66284274495052396768772296973609908596325194702082371577540088149998668),
  (6, 82548149603232055067715153602717548014841108889744000616126365202466390),
  (1, 153572845641813167363524640311644294798703544589012509804796465703772313),
  (7, 168886440257462487804766503558108132014952938817362216743340022472749174),
  (10, 162496718664891552590432413462722100679419742212091253685223022879713566),
  (13, 115176399982092566703165697901299422357565751063819216415240847782394481),
  (6, 23464812984708083251961214877810561828785050182618072726888556255391050)]

private theorem power_205115282021455665897114700593932402728804164701536103180137503955397371_132896956044521568488119 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ 1543415952677955745309227852991199086604869270230 ≠ 1 :=
  trace_power_ne_one 205115282021455665897114700593932402728804164701536103180137503955397371 10 1543415952677955745309227852991199086604869270230 23464812984708083251961214877810561828785050182618072726888556255391050 trace_205115282021455665897114700593932402728804164701536103180137503955397371_132896956044521568488119
    (by decide) (by decide) (by decide) (by decide)

private def trace_205115282021455665897114700593932402728804164701536103180137503955397371_255515944373312847190720520512484175977 : List PowStep := [
  (2, 100),
  (7, 1000000000000000000000000000000000000000),
  (9, 113954088254822619147492528077473037402388743984628826291813118009600612),
  (4, 36573975729055038685151135367456356423605275676104789111019085099987867),
  (1, 179936789471833705038648264199420884425604011111400079280627925643966610),
  (15, 153089690217724706739235891994301669772740529596464384186193238757421494),
  (5, 179645071828990001257777198124783019715446318987932648703290027680482981),
  (7, 164795445419831800873914218567237114486889174605235675023755658061196392),
  (15, 18437007305289626103833306250010088756945495415804171024277234282979550),
  (11, 172067181835293980224908750309248309973070438855938643002492714769373860),
  (3, 29581784120934571787704462644768496587457307523511667983616755708330178),
  (12, 153116296728116285082562006551467298372700964487752245182423875221121088),
  (0, 128272364143708093689978155712465284647937078460732540308561096405330669),
  (3, 76595083799135311875215777641183434363155176378278243626511895121764253),
  (7, 134386242471927737831287717704673305436980249867763963471388227311984762),
  (1, 30892062311928618460937506479751122156344888067222874161660031789928430),
  (8, 146198036565561267470653985397624802796036911280302185972938588647596149),
  (1, 25518074730566470275623244196830775647330771540746787166999375581824285),
  (15, 130423820482416927405379587913493939209456039658486615764978740923698135),
  (12, 48898972969345483282190535536422933353828431078378059873266424864092940),
  (0, 121604353652749118482523074083856535341319218939252511848929376291697229),
  (7, 71492241660756086227287166559656129395394375313821588100507017707923946),
  (15, 89027624064160037237250666371977198500714805676571895142816642529107823),
  (5, 68733900600759969830147258249352365463704161012883414476571981998308310),
  (3, 91632274237544709455557450070153351631299317916261116782512910511450812),
  (3, 40304664404952704584892617065374960408599616399654782520441094522124364),
  (14, 76620902956743746861864219014714725522265757242332387475322755873622395),
  (10, 178266113035923784558209165568976194333480695760850831337861960477148809)]

private theorem power_205115282021455665897114700593932402728804164701536103180137503955397371_255515944373312847190720520512484175977 : (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ 802749442992798076634733441528810 ≠ 1 :=
  trace_power_ne_one 205115282021455665897114700593932402728804164701536103180137503955397371 10 802749442992798076634733441528810 178266113035923784558209165568976194333480695760850831337861960477148809 trace_205115282021455665897114700593932402728804164701536103180137503955397371_255515944373312847190720520512484175977
    (by decide) (by decide) (by decide) (by decide)

theorem prime_205115282021455665897114700593932402728804164701536103180137503955397371 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  let factors : List Nat := [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977]
  have hf : factors.prod = 205115282021455665897114700593932402728804164701536103180137503955397371 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_29, (List.forall_mem_cons.mpr ⟨prime_29, (List.forall_mem_cons.mpr ⟨prime_31, (List.forall_mem_cons.mpr ⟨prime_7723, (List.forall_mem_cons.mpr ⟨prime_132896956044521568488119, (List.forall_mem_cons.mpr ⟨prime_255515944373312847190720520512484175977, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 2) ≠ 1 from power_205115282021455665897114700593932402728804164701536103180137503955397371_2), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 3) ≠ 1 from power_205115282021455665897114700593932402728804164701536103180137503955397371_3), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 5) ≠ 1 from power_205115282021455665897114700593932402728804164701536103180137503955397371_5), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 29) ≠ 1 from power_205115282021455665897114700593932402728804164701536103180137503955397371_29), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 29) ≠ 1 from power_205115282021455665897114700593932402728804164701536103180137503955397371_29), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 31) ≠ 1 from power_205115282021455665897114700593932402728804164701536103180137503955397371_31), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 7723) ≠ 1 from power_205115282021455665897114700593932402728804164701536103180137503955397371_7723), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 132896956044521568488119) ≠ 1 from power_205115282021455665897114700593932402728804164701536103180137503955397371_132896956044521568488119), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ^ ((205115282021455665897114700593932402728804164701536103180137503955397371 - 1) / 255515944373312847190720520512484175977) ≠ 1 from power_205115282021455665897114700593932402728804164701536103180137503955397371_255515944373312847190720520512484175977), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 205115282021455665897114700593932402728804164701536103180137503955397371 (10 : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) power_205115282021455665897114700593932402728804164701536103180137503955397371_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_full : List PowStep := [
  (15, 14348907),
  (15, 30105856329313121259035884688601515868165703272128475446660610094682622685919),
  (15, 71794643963318715608036218650039624470150179724278081743813392558837613215256),
  (15, 75825490713535696747240350438650686524825431256594853763798713930708828166683),
  (15, 49604435221085018032817869343835690591933812321650085495281056731482602298118),
  (15, 86834616403750454157707013149197216848520551420916026383321092385081804250890),
  (15, 105887896764258659276952662117305721322813392689505190890768675541577971813984),
  (15, 74516335229885039589485566714065724942326686180009433743200396012521082294659),
  (15, 86162957004982090191697274328588457603873929354743341831586593709543990342057),
  (15, 7645710761601868312772816518953410687328763093466753960705098736067834484442),
  (15, 601130840265663659726164066847729262794872430685914088364646881919102070693),
  (15, 9268648008456855242032908117486629602634535701776722809744351795517031050940),
  (15, 83835767549100123511111817057124918001038064919081101908545890468453811786093),
  (15, 7555331910264041627427312810122391799082758705982081392267038222892961703142),
  (15, 84239174201391406898242033883099101104077176184154066192966987209607966276529),
  (15, 108306119930645658335354664083643296950446228017306009244529037793989910234332),
  (15, 27274999383634347901972168264595928890529826433998309507273534523182344026730),
  (15, 84376783951569068957142144184186127646328438962291275054413926906067607473971),
  (15, 30469611815857719685704366698720341020109361520900013351830871771138282075670),
  (15, 110171064584971641096775312935249631756500168277306008757159665672019036241472),
  (15, 46693271806322274590839439492310917093233799406525488735137315241636083216621),
  (15, 97327498243939376111032592150557788448834930388381355308183745875347910680598),
  (15, 36797059072100750193917214891380498330767220027832504037582845363355279830330),
  (15, 1840184273345405825971375496254062951331585539363278706738379791196566184967),
  (15, 6740920075408399710445692209875825000921255074859095647586326989785295267197),
  (15, 11224604355223216219816578928360284330181799931966557956178443995383345839910),
  (15, 43348839093928966773442853408861392902993633165608112870133768807549217413494),
  (15, 69790958712381255273060390261305139466314255570864597369013577784149892752340),
  (15, 4261316365436517065384513606131947660575002215442848783069620333608051171068),
  (15, 18650602826337153272426497699720977096950246259664366890335458508273525569050),
  (15, 99466284353601576944077723957837779059666174897492362033631503111001893832284),
  (15, 82297619086740155869927601811707334420917485242375581046961598754408289429963),
  (15, 83751946124124607537372183656136817762194659752037429802739448384835377120282),
  (15, 61751310279739338107859705471513268393979542077488912879007925151183302800597),
  (15, 108301761735064793841600710087718679799500356725191175045323249459193207640585),
  (15, 106733920956904001927318414601459334210177592682673757443461320907472238900886),
  (15, 69346399498793811769302414691317110839580424762017150245342658232335209001993),
  (15, 86939715658156092894429491452620430745699356673775063840794791379116818608887),
  (15, 105107247854697488662747615000098216251462523960291293884383133422624199233728),
  (15, 81093563574320487804972359159857698631389732743376031516258336175788866045510),
  (15, 51334799902789996190085393471424811793521733681217443869863154229325870388705),
  (15, 73229120056850801965621575172857525490635316926307050269201519791139348539768),
  (15, 91073935396130444810347321430881534411593253107997893077237629015241722451268),
  (15, 41039146332361077571016093299842474726759656149550897572006809121488640838591),
  (15, 46940955751518376016629290785470970651078625766736484003699282320597557794732),
  (15, 38615658449441019635786645964423390207346030479066008949192809133143138265314),
  (15, 111066239551095592550830388017723259629543174319080544591905343183149340249371),
  (15, 89994863652766099535261099050774427114615173697201384799264826138602368212595),
  (15, 115285426239102082977918210726057570574228740613326284995966059479504658279973),
  (15, 55793111046691485215539157777329100882205305832067058995909954172367903156843),
  (15, 99031372822903997511896044043919084898956607342378265397076678746352404526515),
  (15, 45226735889489689708178618018621068659737438029818467490748554295230745478091),
  (15, 7362312572142194572437122095577793316911344319837394083732641081262703483528),
  (15, 32310664088876457754287274480568114921628078877469460108441446429534343690319),
  (15, 61941052520569951181669097445377769392206967290492462166653791988881809621913),
  (14, 94954889311071594046208559263246233213951223233604228799367845417979035409939),
  (15, 41590534959420003194111581758072708719459440916836390782199886857485422985903),
  (15, 12669940251844900410163457348128278417874135506095915852838684186395586446748),
  (15, 5920462139285730140946013793257066652780696648260312306954033044494686161016),
  (15, 86863675978851922042085250430643621153089980560023508434018614284414697133860),
  (15, 69738857059812887603079884978267844784686898041148104501892758614024136583980),
  (12, 99801777202535964693565402352400197264468006384428118010463275237293880120346),
  (2, 6099752907902598855186509798543082205652571479031389638685532441804606467364),
  (14, 1)]

private theorem power_115792089237316195423570985008687907853269984665640564039457584007908834671663_full : (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ 115792089237316195423570985008687907853269984665640564039457584007908834671662 = 1 :=
  trace_power 115792089237316195423570985008687907853269984665640564039457584007908834671663 3 115792089237316195423570985008687907853269984665640564039457584007908834671662 1 trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_full
    (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_2 : List PowStep := [
  (7, 2187),
  (15, 3930061525912861057173624287137506221892737197425280369698987),
  (15, 63183110119919744128996689163188981328385030034355215052736362212913650855473),
  (15, 59957056776479137419459608710151106199949775311425997157863253499819622846370),
  (15, 88480900473289722193980917874973040019538387842261714475972000255337388517621),
  (15, 14180509933485250507588415095016499572525871611612937982728808669989933108861),
  (15, 95955785354534149979182044936765440728292188967714258861261063768548331756557),
  (15, 12211832665852729211155933661415708307416444312278466269708249715866946027957),
  (15, 30762923331587499150002708573851714973449420419754564591322656725172434895523),
  (15, 17806482825520629723196672302854306069709932529511775128563369371951025061572),
  (15, 109318385804437916411331610517974063953266358357771021062350731286229545186291),
  (15, 100780302085604862137109646462590150603712756952153938327076285118194273266835),
  (15, 1901025826253364067579540306646597723573017744075746081007910912913226575428),
  (15, 30089688134853910317522825220375176282068948858808106653311324514175312647069),
  (15, 73275759938416195808828801142990470332506841311727693027527925816416099360370),
  (15, 19327362043139599449052665611969911937114369847098452265336033982734477379442),
  (15, 58146147590437240412214493289981346305282815221037581252571667751164775685527),
  (15, 75811765467217929434743319224947415623107140065174258670116538499376951484281),
  (15, 41901237275803048321043463722182309373524053722629588349344802834505538912837),
  (15, 8366158226931911489962558331236170255492124250249007471863238223982995584192),
  (15, 4741563085800889439469909475425232673314418639522684111035925657825749765583),
  (15, 17925863606133487605444866499749482701737759434858437233045150145428428345032),
  (15, 20127450580570066596114621312588629552534547827412663002094019111680441513981),
  (15, 83054680659170870649911193147783121268344490973236627465618824632121676661696),
  (15, 35034746235017470601101318506816132108722505053777531489690177019907704716699),
  (15, 17449339606942554261204035046606427055570878443930722904288767454613327922547),
  (15, 2134009428460577458784990486712270554495579441626814013665737236944577164848),
  (15, 33510561334037531836136449998404011483786196296677608793266881545476302702788),
  (15, 19788928997897920524695813344185238881033772737699007531962824535622872552036),
  (15, 28584158370749448433291265377738836914123758860621072663999738643779314792861),
  (15, 95429258108931895439245828328088857216930852258945434637083250454993662319532),
  (15, 108099113459487428416734848919241580840510365583461178214540880590929694951128),
  (15, 38198939719075496200237781861097757830391738197647124752197071263632456103359),
  (15, 19453960206874517716629317786530710927278767336696542477472550232089436242845),
  (15, 19485125324377464361726806619645113725261580234184934074952369307484169006289),
  (15, 57717876156626536622135946778548577854223856505736871414944987055877098513054),
  (15, 65279663082829544101062033324868274505397708179193662228777918866366086985513),
  (15, 73401570304588797680480944861683069425478526190419976102640700498522769611720),
  (15, 38515193486885585193289438133686290753527296029471720353708958192481152777059),
  (15, 65462585865437930733461213230270529718809188196542515016838622502603891057761),
  (15, 55134352844106326398300473764597170418218491639162754224744297281901304689918),
  (15, 65795230881789038207267243799783320523531320965495424012845057142144477022638),
  (15, 44078272934170886280119691504731920454402794384797401346143267405583864652150),
  (15, 64289415775964534530545235698665504063043278609001723495195602156880649250387),
  (15, 56544702134423290169366299716489419197156474383225901396266208129759066578790),
  (15, 22222076841092754221054786208702281358325142998470687732967587368949461372438),
  (15, 65265810679149880583067405993951940383591027507337432239090520363288459169279),
  (15, 12094773553106172469342326042836796898994262605284010208167879877025821563715),
  (15, 86417071686884411770449249696836079810521989698235333052480229274970130934026),
  (15, 62464267949709752685634483579692971883511399388588122586755518079141129288512),
  (15, 97103567627976161364133666278996516269614206618047222220391696581412780806482),
  (15, 64891726635951470162880640444372440366038333120380485861441430157797536359340),
  (15, 58944304906721450151307013439115240818754356379498593112372347507982523666089),
  (15, 100376907525542055888173563321040053843799492892442598824629890316878355655945),
  (15, 69186213360282099302946539606726083682364158690749442457672793730307646026124),
  (15, 82248426736100380298705839785874549686430720270318739182191941969013792399797),
  (7, 86328729480559204466153248665695785998330678091510829465404590579678141651751),
  (15, 79128715789176063581137379841079230814212746559687069056469037571678424814447),
  (15, 10547617298970417769950467657692899362045913270695961312713079677843893244974),
  (15, 74948684966661729722208269279990140324836870111603787215967101406912553852848),
  (15, 33048567213697236386696810550147135066106717756243420721838026757711097965892),
  (14, 37288097280282374642102299771586338196871719912357661262953906065633988453857),
  (1, 55633922221960477973285768532957107193052186295995703774888801742716568358492),
  (7, 115792089237316195423570985008687907853269984665640564039457584007908834671662)]

private theorem power_115792089237316195423570985008687907853269984665640564039457584007908834671663_2 : (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ 57896044618658097711785492504343953926634992332820282019728792003954417335831 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907853269984665640564039457584007908834671663 3 57896044618658097711785492504343953926634992332820282019728792003954417335831 115792089237316195423570985008687907853269984665640564039457584007908834671662 trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_3 : List PowStep := [
  (5, 243),
  (5, 35917545547686059365808220080151141317043),
  (5, 110325378728090940084759234223828502641333013020690130599532748279764669940972),
  (5, 39673928006117036726787116626566343075105409232533001723155606009939817769320),
  (5, 52474047122537254208847502814056752966630901902031724873614856889826664797724),
  (5, 52771387119296390957918431494276229144484635576199999975887933422588359705290),
  (5, 51942584703941823295467869471583466180063249421822698598402426342668976170563),
  (5, 28056568954097300650336102871853206723907363541715556317688088746333672349621),
  (5, 24018563453686333819758567434919177370549026949935652711009529589992010600774),
  (5, 60056305491124449367328490187084982287353359068929753173302324562763431156725),
  (5, 114142354051237703175931316402194845259347420145752581284443674722027627150386),
  (5, 3005931656411358527800958822964410497349913225998556710154313166545606309927),
  (5, 57772423411334602477065740250769600581221757417374530655070370515542998035423),
  (5, 69387758318398044617311748975661311118804620725791616105816617336251610888555),
  (5, 114645724588497535190774107250955518414854375244609367854471696296824375009778),
  (5, 72872044043911399668489812478291515225596963605185363845252268571775615583922),
  (5, 12796715674088099656488888769380854309139475926205481606225318741869062167585),
  (5, 24279307381727435271586109692680552308837197601411839464611054134735897974288),
  (5, 92606443902681493039154274962240479927095139885745190790896158316651866447126),
  (5, 90751612621910393777772519172971811334867185110758306012240872978988779583165),
  (5, 24060813885030420292575309324917904757642298676100747097154608577615705940020),
  (5, 82606331567904544376222804531372756688329020331630300196485147351337740128745),
  (5, 103522114427120490597045986526679057302186886254400524240776624818697768655039),
  (5, 52524422992216161651691319030524064912409155342761449109034006307668991000538),
  (5, 106684943114157614400202878706463586809723449660741616558350086698283919866520),
  (5, 35338723292275851996002834686525687873615161883251961491411281729279164872815),
  (5, 38750763676288233775506342347364636830032082773002860947267547795337182136071),
  (5, 24838694338796832572574107990740849867564835037651649198838480145523349181062),
  (5, 114556417233576579266123811015824370771891198158850270516729388431924181435552),
  (5, 44354356493386292394561393316478987628789334299771827684726362279618062315722),
  (5, 58682105094089172069351542224713358283172806906022118433195078049320206688818),
  (5, 335305103726182540073460217041831160047108554085958824719279183990495519807),
  (5, 91737167758765134748864235636730739823409998933729921910302800470176536448545),
  (5, 29464591995618262856980004578139579102102291431942087005601505276627145299982),
  (5, 81740057744366914813214583983095497844878715111092646824851538863460352259284),
  (5, 14949857773434411213088873733312657171453791556573855171844478158280439588253),
  (5, 41569856675879215114917145718445799751716680741520858985900819587887894380810),
  (5, 20899688854883229746141000182508760167274318671710746080825302311815449305491),
  (5, 88041119547920491942953440770979423258978757915407361593258718199420443477683),
  (5, 30071020193765033742334577045676616342875284353749128778090475107111947220738),
  (5, 10916485441870819576976719389939007169741437097506810351696965064875991162801),
  (5, 41824728816465822371926653010496264226862246626838634306999758041542004246088),
  (5, 91279048092742197068435797723546017941603688405287790340454900139882654523547),
  (5, 74451414635049909900724265116437668953957764380932685043276931848766704892259),
  (5, 98900829304317681945154838210254296255016781288546555837576460273673397466800),
  (5, 573191967448133944296990616002581273647036714161430734040261352672225945917),
  (5, 64059336063647244194505973105061593440561707481386638492930834868832479308993),
  (5, 23780232559784412760012728515866056959309848032871748249250207270814750667390),
  (5, 67997947420303937313258431163286420429193728811242413621628339981048909941640),
  (5, 11151078638746584973712443407330319552872735401456866406884702224314064999683),
  (5, 22180282921483308030734068441213590797049834708188252986585063306724088453026),
  (5, 6807813688525715958784787020963489979818586220277068566651741223294365363980),
  (5, 66498988391086365554537861335170539260019162950472767070115410896231563876165),
  (5, 8330525417832139553534668174248644013422517517818546600898005116028593990701),
  (5, 32111091042048039307737052438812553205028669773326056825076042642648746134502),
  (4, 79558716608483296698579572878682682520264682815076147828891002757601931437143),
  (15, 25396059063089776062549650102525476773695945177402206784993219425194301680467),
  (15, 56942691911714807812163951455849284865077776178797098914967983523768960176601),
  (15, 61762075376447406500744029385302989491528869932933530786536715926476751927349),
  (15, 108092727813943673466526505118394337660519455487486733725547187084738781353631),
  (15, 98301423371100846747245720047825277864386712251564113923913016161734550104170),
  (14, 89469627384560135851469024648056426821960577787546339981643826402504697274584),
  (11, 85171975419644860939436788151103666358261674890205711764958551494667835944505),
  (10, 60197513588986302554485582024885075108884032450952339817679072026166228089408)]

private theorem power_115792089237316195423570985008687907853269984665640564039457584007908834671663_3 : (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ 38597363079105398474523661669562635951089994888546854679819194669302944890554 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907853269984665640564039457584007908834671663 3 38597363079105398474523661669562635951089994888546854679819194669302944890554 60197513588986302554485582024885075108884032450952339817679072026166228089408 trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_7 : List PowStep := [
  (2, 9),
  (4, 150094635296999121),
  (9, 5340664062370313311267554594558698628119207002378017572099227023379784715089),
  (2, 70364140332093473186806964356584101276906691782603869202472701242699118301808),
  (4, 68965153211664153687264712797884274830501622422192604469794268332968681552505),
  (9, 83529737368565996926491122487180049278705092241559816514266644507467217417959),
  (2, 111615104554655140532714230755029195672925364903740821504132841382810002750871),
  (4, 27786866208903596914201511857049819812521484777957933608385839273476146676679),
  (9, 17016961564893796911743601212775603917775815657918157280322302590359807564812),
  (2, 82533512928879725751027186059670711015873885708325685777683922052652467240907),
  (4, 67400153936308602636632236708995100980174374971270445000319840826898722471829),
  (9, 89338744799610271221964518106720170526941106535835962169964587150761936692623),
  (2, 95021615304149650533773370179182477152242077367527451533919470566795470232350),
  (4, 55564460101779745056000316384828613148370507335630822263511830023869113990920),
  (9, 13828063543877592648304552624529078753548795184000760484977342575089925293000),
  (2, 112032778457143065916487399065970115036029263795379698808974089552041478028467),
  (4, 90673479312907664888281977895171724084927322950980277971292935722034581587846),
  (9, 34532528706546686808068123163185417649698901067657063507066165363012391129796),
  (2, 113981765815349099527677583188723135780627632291559768676766551328046029845239),
  (4, 75527445980630762040604131356819711328189723600593165369129501236272548671984),
  (9, 74903113571186973748142698241273887401049682242129485421553016986028312486067),
  (2, 9504865691026879376759334936969633813195511030917778110186019231039041093528),
  (4, 108258890243568612544027652384698782611177467847687327318251878220586398319828),
  (9, 100266611890269798950576451854339784003941183805102577949849270472126169414675),
  (2, 55611566998837279852207602283044397322418803831199105682247840955056187580114),
  (4, 47076301217069107197765159138608917636005159100458139103285060314097857892199),
  (9, 107222013362598136574167287731295759900369408086876327752994667831555140393989),
  (2, 851522640087022468434820831781035032728093618502452507161735472076379786069),
  (4, 66128502596659876463383447835658717901792547241747213344410881698031633299520),
  (9, 71030487677460431083401410659252152748665853969789144011669125921259995932766),
  (2, 79839315132618446451574544633995576096030327245662863218851411308308375866176),
  (4, 42234059610024454155636883833570810634077950988573481807190287367747933059637),
  (9, 60636273671283484749842587400696228938713938421610329327157732373256683637288),
  (2, 69977689666920163522030116632662281478203217693196094555710159052516885129317),
  (4, 104033424734526706140197719206627296882497352581298551259818374282333685804466),
  (9, 66496201130009232404378522383463489495786199254742828256270079055782089746293),
  (2, 46666440798616337781890101463067697746583464001774766573018168685068963665675),
  (4, 108760596994890515589669997263127950083320889844655727840006853552172674755114),
  (9, 68309216125612248689829326965372911532405938169710887368517257251279163258193),
  (2, 13663643130602664573985461298842718039089828852076319726420879696829388692214),
  (4, 80714748581500229867328501534675370607966468126990725496569887134861212511168),
  (9, 104790958984830549469628077483168804452778075490957568056404279300193048969606),
  (2, 97943500949944418123602092585871372888064477950083794061884693334008035430678),
  (4, 35524262064352828810562835311524497324896956380797072833221938145266447294807),
  (9, 85703379576890729673877682310807191849871368634526208273349038855755317555250),
  (2, 20381585736401224277543001013176405330629103541716875476649900088995745408290),
  (4, 85939783056608638937377987813185796893792583582949013656760574466186154232143),
  (9, 54083289649220703443112724689729049236092883278777505807757146994056017589798),
  (2, 96568885770388196624194595858617924958581039496879245850683910801366652508704),
  (4, 13964215399789316054325883827992910606066745867370748629394304615391048349702),
  (9, 41028155733456593282688284797221032482447413855983219028327058002788299588453),
  (2, 4132363653658831345062560307722813330743698223455433680933880740159498166535),
  (4, 85454678890817472378197376046338232546075706793072428454531729317270766587325),
  (9, 113422625882813904935622714083064149997224702469226386739404229439511727019580),
  (2, 43645625464194034927017552883960423116553282715942735396118100951596059314222),
  (4, 71726614255392616005377741031138650558429136019320859042081662399625142115120),
  (6, 21454774811976636996488349149988086293973065547647376764566730966911531855848),
  (13, 42238921504136483654088936687312387575733976966927355446748213041477379816945),
  (11, 72211591484430676044089816860220367943461413002636756299211193377441233144237),
  (6, 6610217136375996610403045535367662786240351184073998813372107291554505921866),
  (13, 83754287738123370075443143235502077611934558781711239350552098736719758206185),
  (10, 25837442243664888030223285406769590996799320351612590648196608263474493031361),
  (14, 73931739806335891604656979877981700066352554097963002087812489870973795419358),
  (2, 73577166854750709961935200508434814177540983658115200205126683779095497532107)]

private theorem power_115792089237316195423570985008687907853269984665640564039457584007908834671663_7 : (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ 16541727033902313631938712144098272550467140666520080577065369143986976381666 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907853269984665640564039457584007908834671663 3 16541727033902313631938712144098272550467140666520080577065369143986976381666 73577166854750709961935200508434814177540983658115200205126683779095497532107 trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_13441 : List PowStep := [
  (4, 81),
  (14, 16423203268260658146231467800709255289),
  (0, 101172913124326555202011679363038859183578508223927051586990161836422221941567),
  (3, 87754871841103673993312069556443163221180649175430652537759754437793437619002),
  (6, 83407580169437066548891826187768092251244100903549891562819544396141130446120),
  (3, 88897170455041320158866848292736687909906836858023720294577806361546496833237),
  (14, 50532071558504094250541369327220621036819355123211608921563104933848409317263),
  (5, 61899097935223115011622663299919235933556952340281412777923060076025092034209),
  (11, 113075563570526227626624278493957983048592596452876027650385786230085741488542),
  (7, 23637783684435804758662597042385598019494777962123974602777591853871351109738),
  (5, 25003918163592642933990432142800106326073957169084870831144158233531985683917),
  (11, 19350349108759104890858212474950876723726317153227936256384605789510092321716),
  (9, 22063002623247701469411580996008895988657978303792116425065110722993780827173),
  (7, 23632298354571692419557974075413969265745820622726291402243227389289793989143),
  (13, 115289344668552862111937463552361400703648855019076037862830937265664800536059),
  (10, 89233927433689946099318488127713792090344850016221104302739080970688885149130),
  (15, 63966598639508692942782625847250550451184684309309277078748822013316867152660),
  (9, 38152045132807654892572095042277998354232970254518191388158112192206861953222),
  (6, 101958480345369232508237181311810242436550986239529244216237666631919305866732),
  (4, 5279182371030684165544895204346704987088569704437415480774238471220950034287),
  (1, 40452010584052009444200164262736200732045649305654031957540250452771538627623),
  (6, 89205896081911390096510892393479658748664338392733889615231797026651892258719),
  (7, 68788454048461972509113303299255947176639809536865926544633049952212941699175),
  (9, 22938266346696840447934123198851712143664460419074688045268131640617535005626),
  (7, 85210233051313099068390476758973263354346092268443494067379009275694535775539),
  (10, 27106730880346580369731971129445228564846288558225492429995097128469257300010),
  (0, 90419921517601206938997847223033505391173251151426138577594302320458198386967),
  (7, 109526525970247452397137830733520690861660061565281488857792562431575565752300),
  (6, 115544237954406888623869032182151196702482367061996209628469533830140206433425),
  (13, 42709632125215146907768343516721712301578284906195525519351778475143143745700),
  (9, 79943086154014004666110501087583871619508557367132449451645266952357286932985),
  (2, 6347720033846833071070443825354051418115181189134298051599047949648556665654),
  (10, 16674158602183926273600971119659485867094167631951688299636541983129575453263),
  (2, 87048574403765655834014943003700171759615722526509152268440639887896771486896),
  (15, 36807623858007248067434943204236422053037251193810245297472068430154918077945),
  (15, 36743337791552146974781394633519243873684221786659749779416016083530425749976),
  (5, 35682439498808435253452093646859457682651100609755453039394615237569253202395),
  (5, 106929218870610835180167957775045512981018348162360036345777790137208700294544),
  (5, 34105138830711950235500150922015914225418172657450197286533917763425577595412),
  (8, 92647373149910699372349870386250808338879002922103716327740509561443832787385),
  (9, 80682844273996987770259376491647108631749137734561239183792812232183355789892),
  (5, 101367739004117657685193961821161294500128273570007752754113660539507464000636),
  (7, 63370486976225953543462710566935300391718701510337624914396474303448936877915),
  (9, 102301257402339515796710422429075892440636630767789894363029693157486715351147),
  (7, 115719508794356381950691543607482607470821932405246487775455533164404962695080),
  (14, 114847611345018999271212056402862171533266170597127540505559167931395371296676),
  (14, 796857393341336794420429446084032889379929755462074235081590519078995652624),
  (7, 56861747555615863555544555379821008199061709934606980726803328577691460750351),
  (10, 34767176313129744825918122905883206838661995877020337237655082242588024565304),
  (3, 30541694202822740085982810131880460080009670272578198748890408107999593811579),
  (13, 98560810202485430879227862779584412270818811791142466597034922357433465516772),
  (0, 53053207368822288558399686550530052703767303217913617439393575389436170083609),
  (15, 109809711194950153956880645492447522665774823135590166858950100638021162276451),
  (14, 91268869911736059224716281909068954119163212884041187338366849856337652312652),
  (7, 48716788990228052144803131852250674412434676133584222585324125502765663588172),
  (4, 98115330957322505434243584753579994439190044468471367886156897091505263093533),
  (12, 30948306062654001317113346243631765331211142431496180350603780935855867002392),
  (0, 41333971829863700196774792193431463790755531909091405216849405516070124108336),
  (13, 70876834506452697879103968836609092069820560084385847467291086054807683989514),
  (2, 89974218085515020174587143049441291990054665972769678319387424304523317872562),
  (14, 47069427835566023893842355796053529714200560266804286213968496489326012498751)]

private theorem power_115792089237316195423570985008687907853269984665640564039457584007908834671663_13441 : (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ 8614841844901137967678817424945160914609774917464516333565775166126689582 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907853269984665640564039457584007908834671663 3 8614841844901137967678817424945160914609774917464516333565775166126689582 47069427835566023893842355796053529714200560266804286213968496489326012498751 trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_13441
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_205115282021455665897114700593932402728804164701536103180137503955397371 : List PowStep := [
  (8, 6561),
  (9, 232066203043628532565045340531182604896544238770765380550355483363),
  (13, 9142784874946772297449215251484186516344005825986418939695239808468231669128),
  (2, 38950123304404524672521110684256172849797493578065399096721501518692834170181),
  (10, 15008666919421193757556023654256545850754027412553468855825889464239117716646)]

private theorem power_115792089237316195423570985008687907853269984665640564039457584007908834671663_205115282021455665897114700593932402728804164701536103180137503955397371 : (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ 564522 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907853269984665640564039457584007908834671663 3 564522 15008666919421193757556023654256545850754027412553468855825889464239117716646 trace_115792089237316195423570985008687907853269984665640564039457584007908834671663_205115282021455665897114700593932402728804164701536103180137503955397371
    (by decide) (by decide) (by decide) (by decide)

theorem prime_115792089237316195423570985008687907853269984665640564039457584007908834671663 : Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  let factors : List Nat := [2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371]
  have hf : factors.prod = 115792089237316195423570985008687907853269984665640564039457584007908834671663 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_13441, (List.forall_mem_cons.mpr ⟨prime_205115282021455665897114700593932402728804164701536103180137503955397371, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ ((115792089237316195423570985008687907853269984665640564039457584007908834671663 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ ((115792089237316195423570985008687907853269984665640564039457584007908834671663 - 1) / 2) ≠ 1 from power_115792089237316195423570985008687907853269984665640564039457584007908834671663_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ ((115792089237316195423570985008687907853269984665640564039457584007908834671663 - 1) / 3) ≠ 1 from power_115792089237316195423570985008687907853269984665640564039457584007908834671663_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ ((115792089237316195423570985008687907853269984665640564039457584007908834671663 - 1) / 7) ≠ 1 from power_115792089237316195423570985008687907853269984665640564039457584007908834671663_7), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ ((115792089237316195423570985008687907853269984665640564039457584007908834671663 - 1) / 13441) ≠ 1 from power_115792089237316195423570985008687907853269984665640564039457584007908834671663_13441), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ ((115792089237316195423570985008687907853269984665640564039457584007908834671663 - 1) / 205115282021455665897114700593932402728804164701536103180137503955397371) ≠ 1 from power_115792089237316195423570985008687907853269984665640564039457584007908834671663_205115282021455665897114700593932402728804164701536103180137503955397371), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 115792089237316195423570985008687907853269984665640564039457584007908834671663 (3 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) power_115792089237316195423570985008687907853269984665640564039457584007908834671663_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_37 : Nat.Prime 37 := by decide

private def trace_149_full : List PowStep := [
  (9, 65),
  (4, 1)]

private theorem power_149_full : (2 : ZMod 149) ^ 148 = 1 :=
  trace_power 149 2 148 1 trace_149_full
    (by decide) (by decide) (by decide)

private def trace_149_2 : List PowStep := [
  (4, 16),
  (10, 148)]

private theorem power_149_2 : (2 : ZMod 149) ^ 74 ≠ 1 :=
  trace_power_ne_one 149 2 74 148 trace_149_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_149_37 : List PowStep := [
  (4, 16)]

private theorem power_149_37 : (2 : ZMod 149) ^ 4 ≠ 1 :=
  trace_power_ne_one 149 2 4 16 trace_149_37
    (by decide) (by decide) (by decide) (by decide)

theorem prime_149 : Nat.Prime 149 := by
  let factors : List Nat := [2, 2, 37]
  have hf : factors.prod = 149 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_37, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 149) ^ ((149 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 149) ^ ((149 - 1) / 2) ≠ 1 from power_149_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 149) ^ ((149 - 1) / 2) ≠ 1 from power_149_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 149) ^ ((149 - 1) / 37) ≠ 1 from power_149_37), by simp⟩)⟩)⟩)
  apply lucas_primality 149 (2 : ZMod 149) power_149_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_631_full : List PowStep := [
  (2, 9),
  (7, 348),
  (6, 1)]

private theorem power_631_full : (3 : ZMod 631) ^ 630 = 1 :=
  trace_power 631 3 630 1 trace_631_full
    (by decide) (by decide) (by decide)

private def trace_631_2 : List PowStep := [
  (1, 3),
  (3, 482),
  (11, 630)]

private theorem power_631_2 : (3 : ZMod 631) ^ 315 ≠ 1 :=
  trace_power_ne_one 631 3 315 630 trace_631_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_631_3 : List PowStep := [
  (13, 417),
  (2, 587)]

private theorem power_631_3 : (3 : ZMod 631) ^ 210 ≠ 1 :=
  trace_power_ne_one 631 3 210 587 trace_631_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_631_5 : List PowStep := [
  (7, 294),
  (14, 242)]

private theorem power_631_5 : (3 : ZMod 631) ^ 126 ≠ 1 :=
  trace_power_ne_one 631 3 126 242 trace_631_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_631_7 : List PowStep := [
  (5, 243),
  (10, 269)]

private theorem power_631_7 : (3 : ZMod 631) ^ 90 ≠ 1 :=
  trace_power_ne_one 631 3 90 269 trace_631_7
    (by decide) (by decide) (by decide) (by decide)

theorem prime_631 : Nat.Prime 631 := by
  let factors : List Nat := [2, 3, 3, 5, 7]
  have hf : factors.prod = 631 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_7, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 631) ^ ((631 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 631) ^ ((631 - 1) / 2) ≠ 1 from power_631_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 631) ^ ((631 - 1) / 3) ≠ 1 from power_631_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 631) ^ ((631 - 1) / 3) ≠ 1 from power_631_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 631) ^ ((631 - 1) / 5) ≠ 1 from power_631_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 631) ^ ((631 - 1) / 7) ≠ 1 from power_631_7), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 631 (3 : ZMod 631) power_631_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_23 : Nat.Prime 23 := by decide

private def trace_16699_full : List PowStep := [
  (4, 81),
  (1, 4907),
  (3, 4213),
  (10, 1)]

private theorem power_16699_full : (3 : ZMod 16699) ^ 16698 = 1 :=
  trace_power 16699 3 16698 1 trace_16699_full
    (by decide) (by decide) (by decide)

private def trace_16699_2 : List PowStep := [
  (2, 9),
  (0, 8853),
  (9, 11495),
  (13, 16698)]

private theorem power_16699_2 : (3 : ZMod 16699) ^ 8349 ≠ 1 :=
  trace_power_ne_one 16699 3 8349 16698 trace_16699_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_16699_3 : List PowStep := [
  (1, 3),
  (5, 16108),
  (11, 7785),
  (14, 4376)]

private theorem power_16699_3 : (3 : ZMod 16699) ^ 5566 ≠ 1 :=
  trace_power_ne_one 16699 3 5566 4376 trace_16699_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_16699_11 : List PowStep := [
  (5, 243),
  (14, 15124),
  (14, 3130)]

private theorem power_16699_11 : (3 : ZMod 16699) ^ 1518 ≠ 1 :=
  trace_power_ne_one 16699 3 1518 3130 trace_16699_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_16699_23 : List PowStep := [
  (2, 9),
  (13, 12351),
  (6, 7706)]

private theorem power_16699_23 : (3 : ZMod 16699) ^ 726 ≠ 1 :=
  trace_power_ne_one 16699 3 726 7706 trace_16699_23
    (by decide) (by decide) (by decide) (by decide)

theorem prime_16699 : Nat.Prime 16699 := by
  let factors : List Nat := [2, 3, 11, 11, 23]
  have hf : factors.prod = 16699 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_23, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 16699) ^ ((16699 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 16699) ^ ((16699 - 1) / 2) ≠ 1 from power_16699_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 16699) ^ ((16699 - 1) / 3) ≠ 1 from power_16699_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 16699) ^ ((16699 - 1) / 11) ≠ 1 from power_16699_11), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 16699) ^ ((16699 - 1) / 11) ≠ 1 from power_16699_11), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 16699) ^ ((16699 - 1) / 23) ≠ 1 from power_16699_23), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 16699 (3 : ZMod 16699) power_16699_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_2861_full : List PowStep := [
  (11, 2048),
  (2, 1675),
  (12, 1)]

private theorem power_2861_full : (2 : ZMod 2861) ^ 2860 = 1 :=
  trace_power 2861 2 2860 1 trace_2861_full
    (by decide) (by decide) (by decide)

private def trace_2861_2 : List PowStep := [
  (5, 32),
  (9, 1737),
  (6, 2860)]

private theorem power_2861_2 : (2 : ZMod 2861) ^ 1430 ≠ 1 :=
  trace_power_ne_one 2861 2 1430 2860 trace_2861_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_2861_5 : List PowStep := [
  (2, 4),
  (3, 973),
  (12, 2174)]

private theorem power_2861_5 : (2 : ZMod 2861) ^ 572 ≠ 1 :=
  trace_power_ne_one 2861 2 572 2174 trace_2861_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_2861_11 : List PowStep := [
  (1, 2),
  (0, 2594),
  (4, 2368)]

private theorem power_2861_11 : (2 : ZMod 2861) ^ 260 ≠ 1 :=
  trace_power_ne_one 2861 2 260 2368 trace_2861_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_2861_13 : List PowStep := [
  (13, 2470),
  (12, 1385)]

private theorem power_2861_13 : (2 : ZMod 2861) ^ 220 ≠ 1 :=
  trace_power_ne_one 2861 2 220 1385 trace_2861_13
    (by decide) (by decide) (by decide) (by decide)

theorem prime_2861 : Nat.Prime 2861 := by
  let factors : List Nat := [2, 2, 5, 11, 13]
  have hf : factors.prod = 2861 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_13, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 2861) ^ ((2861 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 2861) ^ ((2861 - 1) / 2) ≠ 1 from power_2861_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 2861) ^ ((2861 - 1) / 2) ≠ 1 from power_2861_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 2861) ^ ((2861 - 1) / 5) ≠ 1 from power_2861_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 2861) ^ ((2861 - 1) / 11) ≠ 1 from power_2861_11), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 2861) ^ ((2861 - 1) / 13) ≠ 1 from power_2861_13), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 2861 (2 : ZMod 2861) power_2861_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_85831_full : List PowStep := [
  (1, 3),
  (4, 71688),
  (15, 5312),
  (4, 42046),
  (6, 1)]

private theorem power_85831_full : (3 : ZMod 85831) ^ 85830 = 1 :=
  trace_power 85831 3 85830 1 trace_85831_full
    (by decide) (by decide) (by decide)

private def trace_85831_2 : List PowStep := [
  (10, 59049),
  (7, 50934),
  (10, 5326),
  (3, 85830)]

private theorem power_85831_2 : (3 : ZMod 85831) ^ 42915 ≠ 1 :=
  trace_power_ne_one 85831 3 42915 85830 trace_85831_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_85831_3 : List PowStep := [
  (6, 729),
  (15, 28946),
  (12, 48865),
  (2, 48231)]

private theorem power_85831_3 : (3 : ZMod 85831) ^ 28610 ≠ 1 :=
  trace_power_ne_one 85831 3 28610 48231 trace_85831_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_85831_5 : List PowStep := [
  (4, 81),
  (3, 47114),
  (0, 4507),
  (14, 63649)]

private theorem power_85831_5 : (3 : ZMod 85831) ^ 17166 ≠ 1 :=
  trace_power_ne_one 85831 3 17166 63649 trace_85831_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_85831_2861 : List PowStep := [
  (1, 3),
  (14, 5623)]

private theorem power_85831_2861 : (3 : ZMod 85831) ^ 30 ≠ 1 :=
  trace_power_ne_one 85831 3 30 5623 trace_85831_2861
    (by decide) (by decide) (by decide) (by decide)

theorem prime_85831 : Nat.Prime 85831 := by
  let factors : List Nat := [2, 3, 5, 2861]
  have hf : factors.prod = 85831 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_2861, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 85831) ^ ((85831 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 85831) ^ ((85831 - 1) / 2) ≠ 1 from power_85831_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 85831) ^ ((85831 - 1) / 3) ≠ 1 from power_85831_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 85831) ^ ((85831 - 1) / 5) ≠ 1 from power_85831_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 85831) ^ ((85831 - 1) / 2861) ≠ 1 from power_85831_2861), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 85831 (3 : ZMod 85831) power_85831_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_2011_full : List PowStep := [
  (7, 176),
  (13, 1585),
  (10, 1)]

private theorem power_2011_full : (3 : ZMod 2011) ^ 2010 = 1 :=
  trace_power 2011 3 2010 1 trace_2011_full
    (by decide) (by decide) (by decide)

private def trace_2011_2 : List PowStep := [
  (3, 27),
  (14, 1801),
  (13, 2010)]

private theorem power_2011_2 : (3 : ZMod 2011) ^ 1005 ≠ 1 :=
  trace_power_ne_one 2011 3 1005 2010 trace_2011_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_2011_3 : List PowStep := [
  (2, 9),
  (9, 675),
  (14, 205)]

private theorem power_2011_3 : (3 : ZMod 2011) ^ 670 ≠ 1 :=
  trace_power_ne_one 2011 3 670 205 trace_2011_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_2011_5 : List PowStep := [
  (1, 3),
  (9, 377),
  (2, 1328)]

private theorem power_2011_5 : (3 : ZMod 2011) ^ 402 ≠ 1 :=
  trace_power_ne_one 2011 3 402 1328 trace_2011_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_2011_67 : List PowStep := [
  (1, 3),
  (14, 1116)]

private theorem power_2011_67 : (3 : ZMod 2011) ^ 30 ≠ 1 :=
  trace_power_ne_one 2011 3 30 1116 trace_2011_67
    (by decide) (by decide) (by decide) (by decide)

theorem prime_2011 : Nat.Prime 2011 := by
  let factors : List Nat := [2, 3, 5, 67]
  have hf : factors.prod = 2011 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_67, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 2011) ^ ((2011 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2011) ^ ((2011 - 1) / 2) ≠ 1 from power_2011_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2011) ^ ((2011 - 1) / 3) ≠ 1 from power_2011_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2011) ^ ((2011 - 1) / 5) ≠ 1 from power_2011_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2011) ^ ((2011 - 1) / 67) ≠ 1 from power_2011_67), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 2011 (3 : ZMod 2011) power_2011_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_4681609_full : List PowStep := [
  (4, 279841),
  (7, 4007147),
  (6, 4347332),
  (15, 3089748),
  (8, 4159933),
  (8, 1)]

private theorem power_4681609_full : (23 : ZMod 4681609) ^ 4681608 = 1 :=
  trace_power 4681609 23 4681608 1 trace_4681609_full
    (by decide) (by decide) (by decide)

private def trace_4681609_2 : List PowStep := [
  (2, 529),
  (3, 3706895),
  (11, 4305262),
  (7, 890565),
  (12, 2980310),
  (4, 4681608)]

private theorem power_4681609_2 : (23 : ZMod 4681609) ^ 2340804 ≠ 1 :=
  trace_power_ne_one 4681609 23 2340804 4681608 trace_4681609_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_4681609_3 : List PowStep := [
  (1, 23),
  (7, 1008368),
  (12, 1106182),
  (15, 1493078),
  (13, 2423479),
  (8, 4655375)]

private theorem power_4681609_3 : (23 : ZMod 4681609) ^ 1560536 ≠ 1 :=
  trace_power_ne_one 4681609 23 1560536 4655375 trace_4681609_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_4681609_97 : List PowStep := [
  (11, 486014),
  (12, 3583596),
  (8, 1842712),
  (8, 2645224)]

private theorem power_4681609_97 : (23 : ZMod 4681609) ^ 48264 ≠ 1 :=
  trace_power_ne_one 4681609 23 48264 2645224 trace_4681609_97
    (by decide) (by decide) (by decide) (by decide)

private def trace_4681609_2011 : List PowStep := [
  (9, 1912502),
  (1, 4317713),
  (8, 3128060)]

private theorem power_4681609_2011 : (23 : ZMod 4681609) ^ 2328 ≠ 1 :=
  trace_power_ne_one 4681609 23 2328 3128060 trace_4681609_2011
    (by decide) (by decide) (by decide) (by decide)

theorem prime_4681609 : Nat.Prime 4681609 := by
  let factors : List Nat := [2, 2, 2, 3, 97, 2011]
  have hf : factors.prod = 4681609 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_97, (List.forall_mem_cons.mpr ⟨prime_2011, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (23 : ZMod 4681609) ^ ((4681609 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (23 : ZMod 4681609) ^ ((4681609 - 1) / 2) ≠ 1 from power_4681609_2), (List.forall_mem_cons.mpr ⟨(show (23 : ZMod 4681609) ^ ((4681609 - 1) / 2) ≠ 1 from power_4681609_2), (List.forall_mem_cons.mpr ⟨(show (23 : ZMod 4681609) ^ ((4681609 - 1) / 2) ≠ 1 from power_4681609_2), (List.forall_mem_cons.mpr ⟨(show (23 : ZMod 4681609) ^ ((4681609 - 1) / 3) ≠ 1 from power_4681609_3), (List.forall_mem_cons.mpr ⟨(show (23 : ZMod 4681609) ^ ((4681609 - 1) / 97) ≠ 1 from power_4681609_97), (List.forall_mem_cons.mpr ⟨(show (23 : ZMod 4681609) ^ ((4681609 - 1) / 2011) ≠ 1 from power_4681609_2011), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 4681609 (23 : ZMod 4681609) power_4681609_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_107361793816595537_full : List PowStep := [
  (1, 3),
  (7, 94143178827),
  (13, 36973880021965009),
  (6, 15007446718300619),
  (12, 7346887843953170),
  (15, 83056651816677838),
  (11, 5080375000216447),
  (8, 59618387603825110),
  (14, 87689052603865579),
  (14, 40180309287810751),
  (3, 7072480429533997),
  (0, 36075962105203579),
  (12, 42648670021538053),
  (5, 72473927163104769),
  (0, 1)]

private theorem power_107361793816595537_full : (3 : ZMod 107361793816595537) ^ 107361793816595536 = 1 :=
  trace_power 107361793816595537 3 107361793816595536 1 trace_107361793816595537_full
    (by decide) (by decide) (by decide)

private def trace_107361793816595537_2 : List PowStep := [
  (11, 177147),
  (14, 97779816630901117),
  (11, 43415143153603482),
  (6, 15060109479992554),
  (7, 72513084334753627),
  (13, 93665392188861255),
  (12, 66933677048735527),
  (7, 77572418704653242),
  (7, 92869087647164910),
  (1, 46194939428634179),
  (8, 72881396732049875),
  (6, 95696369144498770),
  (2, 17034641305066342),
  (8, 107361793816595536)]

private theorem power_107361793816595537_2 : (3 : ZMod 107361793816595537) ^ 53680896908297768 ≠ 1 :=
  trace_power_ne_one 107361793816595537 3 53680896908297768 107361793816595536 trace_107361793816595537_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_107361793816595537_16699 : List PowStep := [
  (5, 243),
  (13, 70910607641793623),
  (8, 93075846721186157),
  (14, 6928256710274235),
  (12, 1420104235642634),
  (4, 17826811677868744),
  (3, 39984680933360099),
  (5, 57072672120433796),
  (15, 58415178603988141),
  (15, 65762238575905046),
  (0, 5951470030516601)]

private theorem power_107361793816595537_16699 : (3 : ZMod 107361793816595537) ^ 6429234913264 ≠ 1 :=
  trace_power_ne_one 107361793816595537 3 6429234913264 5951470030516601 trace_107361793816595537_16699
    (by decide) (by decide) (by decide) (by decide)

private def trace_107361793816595537_85831 : List PowStep := [
  (1, 3),
  (2, 387420489),
  (3, 100454543993079131),
  (3, 56853693223952600),
  (12, 37719694642876529),
  (8, 17865319674707720),
  (7, 107260262984205957),
  (13, 85514558252871129),
  (9, 98100946278636549),
  (3, 94434106355880250),
  (0, 43062364984479349)]

private theorem power_107361793816595537_85831 : (3 : ZMod 107361793816595537) ^ 1250851019056 ≠ 1 :=
  trace_power_ne_one 107361793816595537 3 1250851019056 43062364984479349 trace_107361793816595537_85831
    (by decide) (by decide) (by decide) (by decide)

private def trace_107361793816595537_4681609 : List PowStep := [
  (5, 243),
  (5, 70587155515716864),
  (6, 78696938216950808),
  (14, 13615682765701494),
  (4, 3867390421114602),
  (12, 84045033212322675),
  (5, 29504964677063716),
  (13, 83024771148531495),
  (0, 38869239624772579)]

private theorem power_107361793816595537_4681609 : (3 : ZMod 107361793816595537) ^ 22932669904 ≠ 1 :=
  trace_power_ne_one 107361793816595537 3 22932669904 38869239624772579 trace_107361793816595537_4681609
    (by decide) (by decide) (by decide) (by decide)

theorem prime_107361793816595537 : Nat.Prime 107361793816595537 := by
  let factors : List Nat := [2, 2, 2, 2, 16699, 85831, 4681609]
  have hf : factors.prod = 107361793816595537 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_16699, (List.forall_mem_cons.mpr ⟨prime_85831, (List.forall_mem_cons.mpr ⟨prime_4681609, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 107361793816595537) ^ ((107361793816595537 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107361793816595537) ^ ((107361793816595537 - 1) / 2) ≠ 1 from power_107361793816595537_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107361793816595537) ^ ((107361793816595537 - 1) / 2) ≠ 1 from power_107361793816595537_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107361793816595537) ^ ((107361793816595537 - 1) / 2) ≠ 1 from power_107361793816595537_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107361793816595537) ^ ((107361793816595537 - 1) / 2) ≠ 1 from power_107361793816595537_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107361793816595537) ^ ((107361793816595537 - 1) / 16699) ≠ 1 from power_107361793816595537_16699), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107361793816595537) ^ ((107361793816595537 - 1) / 85831) ≠ 1 from power_107361793816595537_85831), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 107361793816595537) ^ ((107361793816595537 - 1) / 4681609) ≠ 1 from power_107361793816595537_4681609), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 107361793816595537 (3 : ZMod 107361793816595537) power_107361793816595537_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_59 : Nat.Prime 59 := by decide

private def trace_4051_full : List PowStep := [
  (15, 2020),
  (13, 1471),
  (2, 1)]

private theorem power_4051_full : (10 : ZMod 4051) ^ 4050 = 1 :=
  trace_power 4051 10 4050 1 trace_4051_full
    (by decide) (by decide) (by decide)

private def trace_4051_2 : List PowStep := [
  (7, 2132),
  (14, 1142),
  (9, 4050)]

private theorem power_4051_2 : (10 : ZMod 4051) ^ 2025 ≠ 1 :=
  trace_power_ne_one 4051 10 2025 4050 trace_4051_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_4051_3 : List PowStep := [
  (5, 2776),
  (4, 261),
  (6, 797)]

private theorem power_4051_3 : (10 : ZMod 4051) ^ 1350 ≠ 1 :=
  trace_power_ne_one 4051 10 1350 797 trace_4051_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_4051_5 : List PowStep := [
  (3, 1000),
  (2, 4008),
  (10, 4019)]

private theorem power_4051_5 : (10 : ZMod 4051) ^ 810 ≠ 1 :=
  trace_power_ne_one 4051 10 810 4019 trace_4051_5
    (by decide) (by decide) (by decide) (by decide)

theorem prime_4051 : Nat.Prime 4051 := by
  let factors : List Nat := [2, 3, 3, 3, 3, 5, 5]
  have hf : factors.prod = 4051 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (10 : ZMod 4051) ^ ((4051 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 4051) ^ ((4051 - 1) / 2) ≠ 1 from power_4051_2), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 4051) ^ ((4051 - 1) / 3) ≠ 1 from power_4051_3), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 4051) ^ ((4051 - 1) / 3) ≠ 1 from power_4051_3), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 4051) ^ ((4051 - 1) / 3) ≠ 1 from power_4051_3), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 4051) ^ ((4051 - 1) / 3) ≠ 1 from power_4051_3), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 4051) ^ ((4051 - 1) / 5) ≠ 1 from power_4051_5), (List.forall_mem_cons.mpr ⟨(show (10 : ZMod 4051) ^ ((4051 - 1) / 5) ≠ 1 from power_4051_5), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 4051 (10 : ZMod 4051) power_4051_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_113_full : List PowStep := [
  (7, 40),
  (0, 1)]

private theorem power_113_full : (3 : ZMod 113) ^ 112 = 1 :=
  trace_power 113 3 112 1 trace_113_full
    (by decide) (by decide) (by decide)

private def trace_113_2 : List PowStep := [
  (3, 27),
  (8, 112)]

private theorem power_113_2 : (3 : ZMod 113) ^ 56 ≠ 1 :=
  trace_power_ne_one 113 3 56 112 trace_113_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_113_7 : List PowStep := [
  (1, 3),
  (0, 49)]

private theorem power_113_7 : (3 : ZMod 113) ^ 16 ≠ 1 :=
  trace_power_ne_one 113 3 16 49 trace_113_7
    (by decide) (by decide) (by decide) (by decide)

theorem prime_113 : Nat.Prime 113 := by
  let factors : List Nat := [2, 2, 2, 2, 7]
  have hf : factors.prod = 113 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_7, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 113) ^ ((113 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 113) ^ ((113 - 1) / 2) ≠ 1 from power_113_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 113) ^ ((113 - 1) / 2) ≠ 1 from power_113_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 113) ^ ((113 - 1) / 2) ≠ 1 from power_113_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 113) ^ ((113 - 1) / 2) ≠ 1 from power_113_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 113) ^ ((113 - 1) / 7) ≠ 1 from power_113_7), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 113 (3 : ZMod 113) power_113_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_120233_full : List PowStep := [
  (1, 3),
  (13, 88878),
  (5, 94472),
  (10, 19559),
  (8, 1)]

private theorem power_120233_full : (3 : ZMod 120233) ^ 120232 = 1 :=
  trace_power 120233 3 120232 1 trace_120233_full
    (by decide) (by decide) (by decide)

private def trace_120233_2 : List PowStep := [
  (14, 93882),
  (10, 25883),
  (13, 84868),
  (4, 120232)]

private theorem power_120233_2 : (3 : ZMod 120233) ^ 60116 ≠ 1 :=
  trace_power_ne_one 120233 3 60116 120232 trace_120233_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_120233_7 : List PowStep := [
  (4, 81),
  (3, 33069),
  (1, 98259),
  (8, 41163)]

private theorem power_120233_7 : (3 : ZMod 120233) ^ 17176 ≠ 1 :=
  trace_power_ne_one 120233 3 17176 41163 trace_120233_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_120233_19 : List PowStep := [
  (1, 3),
  (8, 55287),
  (11, 83809),
  (8, 61639)]

private theorem power_120233_19 : (3 : ZMod 120233) ^ 6328 ≠ 1 :=
  trace_power_ne_one 120233 3 6328 61639 trace_120233_19
    (by decide) (by decide) (by decide) (by decide)

private def trace_120233_113 : List PowStep := [
  (4, 81),
  (2, 11023),
  (8, 80142)]

private theorem power_120233_113 : (3 : ZMod 120233) ^ 1064 ≠ 1 :=
  trace_power_ne_one 120233 3 1064 80142 trace_120233_113
    (by decide) (by decide) (by decide) (by decide)

theorem prime_120233 : Nat.Prime 120233 := by
  let factors : List Nat := [2, 2, 2, 7, 19, 113]
  have hf : factors.prod = 120233 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_19, (List.forall_mem_cons.mpr ⟨prime_113, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 120233) ^ ((120233 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 120233) ^ ((120233 - 1) / 2) ≠ 1 from power_120233_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 120233) ^ ((120233 - 1) / 2) ≠ 1 from power_120233_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 120233) ^ ((120233 - 1) / 2) ≠ 1 from power_120233_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 120233) ^ ((120233 - 1) / 7) ≠ 1 from power_120233_7), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 120233) ^ ((120233 - 1) / 19) ≠ 1 from power_120233_19), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 120233) ^ ((120233 - 1) / 113) ≠ 1 from power_120233_113), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 120233 (3 : ZMod 120233) power_120233_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_199_full : List PowStep := [
  (12, 111),
  (6, 1)]

private theorem power_199_full : (3 : ZMod 199) ^ 198 = 1 :=
  trace_power 199 3 198 1 trace_199_full
    (by decide) (by decide) (by decide)

private def trace_199_2 : List PowStep := [
  (6, 132),
  (3, 198)]

private theorem power_199_2 : (3 : ZMod 199) ^ 99 ≠ 1 :=
  trace_power_ne_one 199 3 99 198 trace_199_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_199_3 : List PowStep := [
  (4, 81),
  (2, 106)]

private theorem power_199_3 : (3 : ZMod 199) ^ 66 ≠ 1 :=
  trace_power_ne_one 199 3 66 106 trace_199_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_199_11 : List PowStep := [
  (1, 3),
  (2, 125)]

private theorem power_199_11 : (3 : ZMod 199) ^ 18 ≠ 1 :=
  trace_power_ne_one 199 3 18 125 trace_199_11
    (by decide) (by decide) (by decide) (by decide)

theorem prime_199 : Nat.Prime 199 := by
  let factors : List Nat := [2, 3, 3, 11]
  have hf : factors.prod = 199 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_11, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 199) ^ ((199 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 199) ^ ((199 - 1) / 2) ≠ 1 from power_199_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 199) ^ ((199 - 1) / 3) ≠ 1 from power_199_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 199) ^ ((199 - 1) / 3) ≠ 1 from power_199_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 199) ^ ((199 - 1) / 11) ≠ 1 from power_199_11), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 199 (3 : ZMod 199) power_199_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_797_full : List PowStep := [
  (3, 8),
  (1, 120),
  (12, 1)]

private theorem power_797_full : (2 : ZMod 797) ^ 796 = 1 :=
  trace_power 797 2 796 1 trace_797_full
    (by decide) (by decide) (by decide)

private def trace_797_2 : List PowStep := [
  (1, 2),
  (8, 366),
  (14, 796)]

private theorem power_797_2 : (2 : ZMod 797) ^ 398 ≠ 1 :=
  trace_power_ne_one 797 2 398 796 trace_797_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_797_199 : List PowStep := [
  (4, 16)]

private theorem power_797_199 : (2 : ZMod 797) ^ 4 ≠ 1 :=
  trace_power_ne_one 797 2 4 16 trace_797_199
    (by decide) (by decide) (by decide) (by decide)

theorem prime_797 : Nat.Prime 797 := by
  let factors : List Nat := [2, 2, 199]
  have hf : factors.prod = 797 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_199, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 797) ^ ((797 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 797) ^ ((797 - 1) / 2) ≠ 1 from power_797_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 797) ^ ((797 - 1) / 2) ≠ 1 from power_797_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 797) ^ ((797 - 1) / 199) ≠ 1 from power_797_199), by simp⟩)⟩)⟩)
  apply lucas_primality 797 (2 : ZMod 797) power_797_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_41 : Nat.Prime 41 := by decide

private def trace_9349_full : List PowStep := [
  (2, 4),
  (4, 7498),
  (8, 346),
  (4, 1)]

private theorem power_9349_full : (2 : ZMod 9349) ^ 9348 = 1 :=
  trace_power 9349 2 9348 1 trace_9349_full
    (by decide) (by decide) (by decide)

private def trace_9349_2 : List PowStep := [
  (1, 2),
  (2, 372),
  (4, 9211),
  (2, 9348)]

private theorem power_9349_2 : (2 : ZMod 9349) ^ 4674 ≠ 1 :=
  trace_power_ne_one 9349 2 4674 9348 trace_9349_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_9349_3 : List PowStep := [
  (12, 4096),
  (2, 6193),
  (12, 4020)]

private theorem power_9349_3 : (2 : ZMod 9349) ^ 3116 ≠ 1 :=
  trace_power_ne_one 9349 2 3116 4020 trace_9349_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_9349_19 : List PowStep := [
  (1, 2),
  (14, 9174),
  (12, 4423)]

private theorem power_9349_19 : (2 : ZMod 9349) ^ 492 ≠ 1 :=
  trace_power_ne_one 9349 2 492 4423 trace_9349_19
    (by decide) (by decide) (by decide) (by decide)

private def trace_9349_41 : List PowStep := [
  (14, 7035),
  (4, 1995)]

private theorem power_9349_41 : (2 : ZMod 9349) ^ 228 ≠ 1 :=
  trace_power_ne_one 9349 2 228 1995 trace_9349_41
    (by decide) (by decide) (by decide) (by decide)

theorem prime_9349 : Nat.Prime 9349 := by
  let factors : List Nat := [2, 2, 3, 19, 41]
  have hf : factors.prod = 9349 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_19, (List.forall_mem_cons.mpr ⟨prime_41, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 9349) ^ ((9349 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 9349) ^ ((9349 - 1) / 2) ≠ 1 from power_9349_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 9349) ^ ((9349 - 1) / 2) ≠ 1 from power_9349_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 9349) ^ ((9349 - 1) / 3) ≠ 1 from power_9349_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 9349) ^ ((9349 - 1) / 19) ≠ 1 from power_9349_19), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 9349) ^ ((9349 - 1) / 41) ≠ 1 from power_9349_41), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 9349 (2 : ZMod 9349) power_9349_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_44706919_full : List PowStep := [
  (2, 36),
  (10, 11142169),
  (10, 11156122),
  (2, 30381490),
  (12, 36697249),
  (6, 3961136),
  (6, 1)]

private theorem power_44706919_full : (6 : ZMod 44706919) ^ 44706918 = 1 :=
  trace_power 44706919 6 44706918 1 trace_44706919_full
    (by decide) (by decide) (by decide)

private def trace_44706919_2 : List PowStep := [
  (1, 6),
  (5, 21757026),
  (5, 13745894),
  (1, 41939341),
  (6, 10785951),
  (3, 24456899),
  (3, 44706918)]

private theorem power_44706919_2 : (6 : ZMod 44706919) ^ 22353459 ≠ 1 :=
  trace_power_ne_one 44706919 6 22353459 44706918 trace_44706919_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_44706919_3 : List PowStep := [
  (14, 37642008),
  (3, 8718243),
  (6, 198857),
  (4, 6641011),
  (2, 36146674),
  (2, 30500379)]

private theorem power_44706919_3 : (6 : ZMod 44706919) ^ 14902306 ≠ 1 :=
  trace_power_ne_one 44706919 6 14902306 30500379 trace_44706919_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_44706919_797 : List PowStep := [
  (13, 6273668),
  (11, 34946530),
  (1, 23167218),
  (14, 41156332)]

private theorem power_44706919_797 : (6 : ZMod 44706919) ^ 56094 ≠ 1 :=
  trace_power_ne_one 44706919 6 56094 41156332 trace_44706919_797
    (by decide) (by decide) (by decide) (by decide)

private def trace_44706919_9349 : List PowStep := [
  (1, 6),
  (2, 8793739),
  (10, 15677846),
  (14, 6711465)]

private theorem power_44706919_9349 : (6 : ZMod 44706919) ^ 4782 ≠ 1 :=
  trace_power_ne_one 44706919 6 4782 6711465 trace_44706919_9349
    (by decide) (by decide) (by decide) (by decide)

theorem prime_44706919 : Nat.Prime 44706919 := by
  let factors : List Nat := [2, 3, 797, 9349]
  have hf : factors.prod = 44706919 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_797, (List.forall_mem_cons.mpr ⟨prime_9349, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (6 : ZMod 44706919) ^ ((44706919 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 44706919) ^ ((44706919 - 1) / 2) ≠ 1 from power_44706919_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 44706919) ^ ((44706919 - 1) / 3) ≠ 1 from power_44706919_3), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 44706919) ^ ((44706919 - 1) / 797) ≠ 1 from power_44706919_797), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 44706919) ^ ((44706919 - 1) / 9349) ≠ 1 from power_44706919_9349), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 44706919 (6 : ZMod 44706919) power_44706919_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_174723607534414371449_full : List PowStep := [
  (9, 19683),
  (7, 21827226346846568916),
  (8, 80783379045843909668),
  (12, 89172960959100719934),
  (6, 89176769481209891563),
  (15, 30591791567077660644),
  (3, 173893491639640282859),
  (5, 134221866499276525782),
  (3, 1126810941039892147),
  (12, 50074366886815019389),
  (3, 111622343558947154876),
  (8, 22449081314743798006),
  (8, 119070985234446425622),
  (9, 113022943096300677303),
  (10, 59990724495109190965),
  (7, 53090047975370130565),
  (8, 1)]

private theorem power_174723607534414371449_full : (3 : ZMod 174723607534414371449) ^ 174723607534414371448 = 1 :=
  trace_power 174723607534414371449 3 174723607534414371448 1 trace_174723607534414371449_full
    (by decide) (by decide) (by decide)

private def trace_174723607534414371449_2 : List PowStep := [
  (4, 81),
  (11, 39450300670676347197),
  (12, 110987815163846297970),
  (6, 4464350277151350878),
  (3, 91160004434626511252),
  (7, 56666247249569737688),
  (9, 87056930269274094615),
  (10, 75761248899506877784),
  (9, 76033498948856616413),
  (14, 138522363489388832291),
  (1, 125163612706440726615),
  (12, 51096433175842570065),
  (4, 148278493275165466050),
  (4, 132869844669731492544),
  (13, 75856209096091021632),
  (3, 149194188765239834736),
  (12, 174723607534414371448)]

private theorem power_174723607534414371449_2 : (3 : ZMod 174723607534414371449) ^ 87361803767207185724 ≠ 1 :=
  trace_power_ne_one 174723607534414371449 3 87361803767207185724 174723607534414371448 trace_174723607534414371449_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_174723607534414371449_17 : List PowStep := [
  (8, 6561),
  (14, 30013836523914130795),
  (10, 111873604833179861391),
  (2, 63953821059434370005),
  (4, 93021563209947840473),
  (10, 98734546313635294387),
  (8, 133539822172086033107),
  (12, 31957171164049472721),
  (7, 64662009733228114615),
  (4, 62783356252809651089),
  (14, 27874971342669344084),
  (9, 20644660432904114957),
  (14, 162523323671806407736),
  (10, 120374736777610379473),
  (15, 167459909583720292773),
  (8, 143977312736193201955)]

private theorem power_174723607534414371449_17 : (3 : ZMod 174723607534414371449) ^ 10277859266730257144 ≠ 1 :=
  trace_power_ne_one 174723607534414371449 3 10277859266730257144 143977312736193201955 trace_174723607534414371449_17
    (by decide) (by decide) (by decide) (by decide)

private def trace_174723607534414371449_59 : List PowStep := [
  (2, 9),
  (9, 36472996377170786403),
  (1, 71115838072904138925),
  (9, 18816665753391739402),
  (1, 88419022740501594028),
  (1, 105499106087607615339),
  (2, 49646316312993611610),
  (4, 8867001942462856302),
  (2, 81501343755733135309),
  (1, 68571764208794914260),
  (10, 71483936067855344891),
  (15, 123289639534365361577),
  (13, 156675374419378091656),
  (15, 66613474109212028672),
  (14, 130633109131128675941),
  (8, 101275312590739994117)]

private theorem power_174723607534414371449_59 : (3 : ZMod 174723607534414371449) ^ 2961417076854480872 ≠ 1 :=
  trace_power_ne_one 174723607534414371449 3 2961417076854480872 101275312590739994117 trace_174723607534414371449_59
    (by decide) (by decide) (by decide) (by decide)

private def trace_174723607534414371449_4051 : List PowStep := [
  (9, 19683),
  (9, 21721429587204748795),
  (3, 34808023968231081469),
  (11, 14130155677545042094),
  (6, 114850476837257878127),
  (6, 159723822702433688338),
  (4, 3150364979060956627),
  (4, 67056117972681967735),
  (13, 76705067690402025733),
  (13, 154804597392616084858),
  (14, 47199920269040191265),
  (8, 25149010327877481718),
  (10, 91480088942839378770),
  (8, 117775491988442121468)]

private theorem power_174723607534414371449_4051 : (3 : ZMod 174723607534414371449) ^ 43130981864827048 ≠ 1 :=
  trace_power_ne_one 174723607534414371449 3 43130981864827048 117775491988442121468 trace_174723607534414371449_4051
    (by decide) (by decide) (by decide) (by decide)

private def trace_174723607534414371449_120233 : List PowStep := [
  (5, 243),
  (2, 139069052302886195482),
  (9, 81435487474654938275),
  (10, 173336698374535822876),
  (15, 173856563625160866589),
  (7, 9357580879012739809),
  (3, 37965302272605155446),
  (7, 98856857102360559315),
  (2, 28737638441035579552),
  (6, 87528089657033610942),
  (1, 137124700468162548153),
  (11, 139158170247318301475),
  (8, 143725591556162883674)]

private theorem power_174723607534414371449_120233 : (3 : ZMod 174723607534414371449) ^ 1453208416444856 ≠ 1 :=
  trace_power_ne_one 174723607534414371449 3 1453208416444856 143725591556162883674 trace_174723607534414371449_120233
    (by decide) (by decide) (by decide) (by decide)

private def trace_174723607534414371449_44706919 : List PowStep := [
  (3, 27),
  (8, 108062819583384779209),
  (13, 153951483820610241231),
  (15, 29434902586356298294),
  (2, 113424935163739021047),
  (14, 3681033083788750562),
  (8, 95256284950967220619),
  (8, 37388551213422755613),
  (6, 5343755608700306106),
  (12, 29210414515818610392),
  (8, 72059039805266995621)]

private theorem power_174723607534414371449_44706919 : (3 : ZMod 174723607534414371449) ^ 3908200597192 ≠ 1 :=
  trace_power_ne_one 174723607534414371449 3 3908200597192 72059039805266995621 trace_174723607534414371449_44706919
    (by decide) (by decide) (by decide) (by decide)

theorem prime_174723607534414371449 : Nat.Prime 174723607534414371449 := by
  let factors : List Nat := [2, 2, 2, 17, 59, 4051, 120233, 44706919]
  have hf : factors.prod = 174723607534414371449 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_17, (List.forall_mem_cons.mpr ⟨prime_59, (List.forall_mem_cons.mpr ⟨prime_4051, (List.forall_mem_cons.mpr ⟨prime_120233, (List.forall_mem_cons.mpr ⟨prime_44706919, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 174723607534414371449) ^ ((174723607534414371449 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 174723607534414371449) ^ ((174723607534414371449 - 1) / 2) ≠ 1 from power_174723607534414371449_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 174723607534414371449) ^ ((174723607534414371449 - 1) / 2) ≠ 1 from power_174723607534414371449_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 174723607534414371449) ^ ((174723607534414371449 - 1) / 2) ≠ 1 from power_174723607534414371449_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 174723607534414371449) ^ ((174723607534414371449 - 1) / 17) ≠ 1 from power_174723607534414371449_17), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 174723607534414371449) ^ ((174723607534414371449 - 1) / 59) ≠ 1 from power_174723607534414371449_59), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 174723607534414371449) ^ ((174723607534414371449 - 1) / 4051) ≠ 1 from power_174723607534414371449_4051), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 174723607534414371449) ^ ((174723607534414371449 - 1) / 120233) ≠ 1 from power_174723607534414371449_120233), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 174723607534414371449) ^ ((174723607534414371449 - 1) / 44706919) ≠ 1 from power_174723607534414371449_44706919), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 174723607534414371449 (3 : ZMod 174723607534414371449) power_174723607534414371449_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_109_full : List PowStep := [
  (6, 4),
  (12, 1)]

private theorem power_109_full : (6 : ZMod 109) ^ 108 = 1 :=
  trace_power 109 6 108 1 trace_109_full
    (by decide) (by decide) (by decide)

private def trace_109_2 : List PowStep := [
  (3, 107),
  (6, 108)]

private theorem power_109_2 : (6 : ZMod 109) ^ 54 ≠ 1 :=
  trace_power_ne_one 109 6 54 108 trace_109_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_109_3 : List PowStep := [
  (2, 36),
  (4, 63)]

private theorem power_109_3 : (6 : ZMod 109) ^ 36 ≠ 1 :=
  trace_power_ne_one 109 6 36 63 trace_109_3
    (by decide) (by decide) (by decide) (by decide)

theorem prime_109 : Nat.Prime 109 := by
  let factors : List Nat := [2, 2, 3, 3, 3]
  have hf : factors.prod = 109 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (6 : ZMod 109) ^ ((109 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 109) ^ ((109 - 1) / 2) ≠ 1 from power_109_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 109) ^ ((109 - 1) / 2) ≠ 1 from power_109_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 109) ^ ((109 - 1) / 3) ≠ 1 from power_109_3), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 109) ^ ((109 - 1) / 3) ≠ 1 from power_109_3), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 109) ^ ((109 - 1) / 3) ≠ 1 from power_109_3), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 109 (6 : ZMod 109) power_109_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_73 : Nat.Prime 73 := by decide

private def trace_293_full : List PowStep := [
  (1, 2),
  (2, 202),
  (4, 1)]

private theorem power_293_full : (2 : ZMod 293) ^ 292 = 1 :=
  trace_power 293 2 292 1 trace_293_full
    (by decide) (by decide) (by decide)

private def trace_293_2 : List PowStep := [
  (9, 219),
  (2, 292)]

private theorem power_293_2 : (2 : ZMod 293) ^ 146 ≠ 1 :=
  trace_power_ne_one 293 2 146 292 trace_293_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_293_73 : List PowStep := [
  (4, 16)]

private theorem power_293_73 : (2 : ZMod 293) ^ 4 ≠ 1 :=
  trace_power_ne_one 293 2 4 16 trace_293_73
    (by decide) (by decide) (by decide) (by decide)

theorem prime_293 : Nat.Prime 293 := by
  let factors : List Nat := [2, 2, 73]
  have hf : factors.prod = 293 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_73, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 293) ^ ((293 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 293) ^ ((293 - 1) / 2) ≠ 1 from power_293_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 293) ^ ((293 - 1) / 2) ≠ 1 from power_293_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 293) ^ ((293 - 1) / 73) ≠ 1 from power_293_73), by simp⟩)⟩)⟩)
  apply lucas_primality 293 (2 : ZMod 293) power_293_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_2731_full : List PowStep := [
  (10, 1698),
  (10, 2693),
  (10, 1)]

private theorem power_2731_full : (3 : ZMod 2731) ^ 2730 = 1 :=
  trace_power 2731 3 2730 1 trace_2731_full
    (by decide) (by decide) (by decide)

private def trace_2731_2 : List PowStep := [
  (5, 243),
  (5, 1552),
  (5, 2730)]

private theorem power_2731_2 : (3 : ZMod 2731) ^ 1365 ≠ 1 :=
  trace_power_ne_one 2731 3 1365 2730 trace_2731_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_2731_3 : List PowStep := [
  (3, 27),
  (8, 712),
  (14, 2284)]

private theorem power_2731_3 : (3 : ZMod 2731) ^ 910 ≠ 1 :=
  trace_power_ne_one 2731 3 910 2284 trace_2731_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_2731_5 : List PowStep := [
  (2, 9),
  (2, 499),
  (2, 1633)]

private theorem power_2731_5 : (3 : ZMod 2731) ^ 546 ≠ 1 :=
  trace_power_ne_one 2731 3 546 1633 trace_2731_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_2731_7 : List PowStep := [
  (1, 3),
  (8, 790),
  (6, 1238)]

private theorem power_2731_7 : (3 : ZMod 2731) ^ 390 ≠ 1 :=
  trace_power_ne_one 2731 3 390 1238 trace_2731_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_2731_13 : List PowStep := [
  (13, 2150),
  (2, 1024)]

private theorem power_2731_13 : (3 : ZMod 2731) ^ 210 ≠ 1 :=
  trace_power_ne_one 2731 3 210 1024 trace_2731_13
    (by decide) (by decide) (by decide) (by decide)

theorem prime_2731 : Nat.Prime 2731 := by
  let factors : List Nat := [2, 3, 5, 7, 13]
  have hf : factors.prod = 2731 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_13, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 2731) ^ ((2731 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2731) ^ ((2731 - 1) / 2) ≠ 1 from power_2731_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2731) ^ ((2731 - 1) / 3) ≠ 1 from power_2731_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2731) ^ ((2731 - 1) / 5) ≠ 1 from power_2731_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2731) ^ ((2731 - 1) / 7) ≠ 1 from power_2731_7), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 2731) ^ ((2731 - 1) / 13) ≠ 1 from power_2731_13), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 2731 (3 : ZMod 2731) power_2731_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_305873_full : List PowStep := [
  (4, 81),
  (10, 90915),
  (10, 24166),
  (13, 260451),
  (0, 1)]

private theorem power_305873_full : (3 : ZMod 305873) ^ 305872 = 1 :=
  trace_power 305873 3 305872 1 trace_305873_full
    (by decide) (by decide) (by decide)

private def trace_305873_2 : List PowStep := [
  (2, 9),
  (5, 214397),
  (5, 108989),
  (6, 12221),
  (8, 305872)]

private theorem power_305873_2 : (3 : ZMod 305873) ^ 152936 ≠ 1 :=
  trace_power_ne_one 305873 3 152936 305872 trace_305873_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_305873_7 : List PowStep := [
  (10, 59049),
  (10, 247145),
  (11, 77904),
  (0, 145208)]

private theorem power_305873_7 : (3 : ZMod 305873) ^ 43696 ≠ 1 :=
  trace_power_ne_one 305873 3 43696 145208 trace_305873_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_305873_2731 : List PowStep := [
  (7, 2187),
  (0, 133117)]

private theorem power_305873_2731 : (3 : ZMod 305873) ^ 112 ≠ 1 :=
  trace_power_ne_one 305873 3 112 133117 trace_305873_2731
    (by decide) (by decide) (by decide) (by decide)

theorem prime_305873 : Nat.Prime 305873 := by
  let factors : List Nat := [2, 2, 2, 2, 7, 2731]
  have hf : factors.prod = 305873 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_2731, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 305873) ^ ((305873 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 305873) ^ ((305873 - 1) / 2) ≠ 1 from power_305873_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 305873) ^ ((305873 - 1) / 2) ≠ 1 from power_305873_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 305873) ^ ((305873 - 1) / 2) ≠ 1 from power_305873_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 305873) ^ ((305873 - 1) / 2) ≠ 1 from power_305873_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 305873) ^ ((305873 - 1) / 7) ≠ 1 from power_305873_7), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 305873) ^ ((305873 - 1) / 2731) ≠ 1 from power_305873_2731), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 305873 (3 : ZMod 305873) power_305873_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_1409_full : List PowStep := [
  (5, 243),
  (8, 1254),
  (0, 1)]

private theorem power_1409_full : (3 : ZMod 1409) ^ 1408 = 1 :=
  trace_power 1409 3 1408 1 trace_1409_full
    (by decide) (by decide) (by decide)

private def trace_1409_2 : List PowStep := [
  (2, 9),
  (12, 327),
  (0, 1408)]

private theorem power_1409_2 : (3 : ZMod 1409) ^ 704 ≠ 1 :=
  trace_power_ne_one 1409 3 704 1408 trace_1409_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_1409_11 : List PowStep := [
  (8, 925),
  (0, 992)]

private theorem power_1409_11 : (3 : ZMod 1409) ^ 128 ≠ 1 :=
  trace_power_ne_one 1409 3 128 992 trace_1409_11
    (by decide) (by decide) (by decide) (by decide)

theorem prime_1409 : Nat.Prime 1409 := by
  let factors : List Nat := [2, 2, 2, 2, 2, 2, 2, 11]
  have hf : factors.prod = 1409 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_11, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 1409) ^ ((1409 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1409) ^ ((1409 - 1) / 2) ≠ 1 from power_1409_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1409) ^ ((1409 - 1) / 2) ≠ 1 from power_1409_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1409) ^ ((1409 - 1) / 2) ≠ 1 from power_1409_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1409) ^ ((1409 - 1) / 2) ≠ 1 from power_1409_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1409) ^ ((1409 - 1) / 2) ≠ 1 from power_1409_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1409) ^ ((1409 - 1) / 2) ≠ 1 from power_1409_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1409) ^ ((1409 - 1) / 2) ≠ 1 from power_1409_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1409) ^ ((1409 - 1) / 11) ≠ 1 from power_1409_11), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 1409 (3 : ZMod 1409) power_1409_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_28181_full : List PowStep := [
  (6, 64),
  (14, 22781),
  (1, 1871),
  (4, 1)]

private theorem power_28181_full : (2 : ZMod 28181) ^ 28180 = 1 :=
  trace_power 28181 2 28180 1 trace_28181_full
    (by decide) (by decide) (by decide)

private def trace_28181_2 : List PowStep := [
  (3, 8),
  (7, 24413),
  (0, 14874),
  (10, 28180)]

private theorem power_28181_2 : (2 : ZMod 28181) ^ 14090 ≠ 1 :=
  trace_power_ne_one 28181 2 14090 28180 trace_28181_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_28181_5 : List PowStep := [
  (1, 2),
  (6, 23516),
  (0, 12198),
  (4, 26799)]

private theorem power_28181_5 : (2 : ZMod 28181) ^ 5636 ≠ 1 :=
  trace_power_ne_one 28181 2 5636 26799 trace_28181_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_28181_1409 : List PowStep := [
  (1, 2),
  (4, 5879)]

private theorem power_28181_1409 : (2 : ZMod 28181) ^ 20 ≠ 1 :=
  trace_power_ne_one 28181 2 20 5879 trace_28181_1409
    (by decide) (by decide) (by decide) (by decide)

theorem prime_28181 : Nat.Prime 28181 := by
  let factors : List Nat := [2, 2, 5, 1409]
  have hf : factors.prod = 28181 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_1409, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 28181) ^ ((28181 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 28181) ^ ((28181 - 1) / 2) ≠ 1 from power_28181_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 28181) ^ ((28181 - 1) / 2) ≠ 1 from power_28181_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 28181) ^ ((28181 - 1) / 5) ≠ 1 from power_28181_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 28181) ^ ((28181 - 1) / 1409) ≠ 1 from power_28181_1409), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 28181 (2 : ZMod 28181) power_28181_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_545358713_full : List PowStep := [
  (2, 25),
  (0, 537090061),
  (8, 329825877),
  (1, 221484038),
  (8, 202352910),
  (3, 402166313),
  (7, 76704037),
  (8, 1)]

private theorem power_545358713_full : (5 : ZMod 545358713) ^ 545358712 = 1 :=
  trace_power 545358713 5 545358712 1 trace_545358713_full
    (by decide) (by decide) (by decide)

private def trace_545358713_2 : List PowStep := [
  (1, 5),
  (0, 432809698),
  (4, 508556794),
  (0, 224801326),
  (12, 74656036),
  (1, 44432862),
  (11, 231231617),
  (12, 545358712)]

private theorem power_545358713_2 : (5 : ZMod 545358713) ^ 272679356 ≠ 1 :=
  trace_power_ne_one 545358713 5 272679356 545358712 trace_545358713_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_545358713_41 : List PowStep := [
  (12, 244140625),
  (10, 238120006),
  (15, 474543994),
  (6, 475789516),
  (11, 456592726),
  (8, 232418614)]

private theorem power_545358713_41 : (5 : ZMod 545358713) ^ 13301432 ≠ 1 :=
  trace_power_ne_one 545358713 5 13301432 232418614 trace_545358713_41
    (by decide) (by decide) (by decide) (by decide)

private def trace_545358713_59 : List PowStep := [
  (8, 390625),
  (13, 526097736),
  (0, 209981595),
  (10, 210473103),
  (14, 284648826),
  (8, 256734421)]

private theorem power_545358713_59 : (5 : ZMod 545358713) ^ 9243368 ≠ 1 :=
  trace_power_ne_one 545358713 5 9243368 256734421 trace_545358713_59
    (by decide) (by decide) (by decide) (by decide)

private def trace_545358713_28181 : List PowStep := [
  (4, 625),
  (11, 521943090),
  (9, 83579703),
  (8, 453985277)]

private theorem power_545358713_28181 : (5 : ZMod 545358713) ^ 19352 ≠ 1 :=
  trace_power_ne_one 545358713 5 19352 453985277 trace_545358713_28181
    (by decide) (by decide) (by decide) (by decide)

theorem prime_545358713 : Nat.Prime 545358713 := by
  let factors : List Nat := [2, 2, 2, 41, 59, 28181]
  have hf : factors.prod = 545358713 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_41, (List.forall_mem_cons.mpr ⟨prime_59, (List.forall_mem_cons.mpr ⟨prime_28181, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (5 : ZMod 545358713) ^ ((545358713 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 545358713) ^ ((545358713 - 1) / 2) ≠ 1 from power_545358713_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 545358713) ^ ((545358713 - 1) / 2) ≠ 1 from power_545358713_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 545358713) ^ ((545358713 - 1) / 2) ≠ 1 from power_545358713_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 545358713) ^ ((545358713 - 1) / 41) ≠ 1 from power_545358713_41), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 545358713) ^ ((545358713 - 1) / 59) ≠ 1 from power_545358713_59), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 545358713) ^ ((545358713 - 1) / 28181) ≠ 1 from power_545358713_28181), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 545358713 (5 : ZMod 545358713) power_545358713_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_461_full : List PowStep := [
  (1, 2),
  (12, 227),
  (12, 1)]

private theorem power_461_full : (2 : ZMod 461) ^ 460 = 1 :=
  trace_power 461 2 460 1 trace_461_full
    (by decide) (by decide) (by decide)

private def trace_461_2 : List PowStep := [
  (14, 249),
  (6, 460)]

private theorem power_461_2 : (2 : ZMod 461) ^ 230 ≠ 1 :=
  trace_power_ne_one 461 2 230 460 trace_461_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_461_5 : List PowStep := [
  (5, 32),
  (12, 88)]

private theorem power_461_5 : (2 : ZMod 461) ^ 92 ≠ 1 :=
  trace_power_ne_one 461 2 92 88 trace_461_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_461_23 : List PowStep := [
  (1, 2),
  (4, 262)]

private theorem power_461_23 : (2 : ZMod 461) ^ 20 ≠ 1 :=
  trace_power_ne_one 461 2 20 262 trace_461_23
    (by decide) (by decide) (by decide) (by decide)

theorem prime_461 : Nat.Prime 461 := by
  let factors : List Nat := [2, 2, 5, 23]
  have hf : factors.prod = 461 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_23, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 461) ^ ((461 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 461) ^ ((461 - 1) / 2) ≠ 1 from power_461_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 461) ^ ((461 - 1) / 2) ≠ 1 from power_461_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 461) ^ ((461 - 1) / 5) ≠ 1 from power_461_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 461) ^ ((461 - 1) / 23) ≠ 1 from power_461_23), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 461 (2 : ZMod 461) power_461_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_1871_full : List PowStep := [
  (7, 1364),
  (4, 675),
  (14, 1)]

private theorem power_1871_full : (14 : ZMod 1871) ^ 1870 = 1 :=
  trace_power 1871 14 1870 1 trace_1871_full
    (by decide) (by decide) (by decide)

private def trace_1871_2 : List PowStep := [
  (3, 873),
  (10, 1498),
  (7, 1870)]

private theorem power_1871_2 : (14 : ZMod 1871) ^ 935 ≠ 1 :=
  trace_power_ne_one 1871 14 935 1870 trace_1871_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_1871_5 : List PowStep := [
  (1, 14),
  (7, 653),
  (6, 932)]

private theorem power_1871_5 : (14 : ZMod 1871) ^ 374 ≠ 1 :=
  trace_power_ne_one 1871 14 374 932 trace_1871_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_1871_11 : List PowStep := [
  (10, 816),
  (10, 1838)]

private theorem power_1871_11 : (14 : ZMod 1871) ^ 170 ≠ 1 :=
  trace_power_ne_one 1871 14 170 1838 trace_1871_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_1871_17 : List PowStep := [
  (6, 632),
  (14, 81)]

private theorem power_1871_17 : (14 : ZMod 1871) ^ 110 ≠ 1 :=
  trace_power_ne_one 1871 14 110 81 trace_1871_17
    (by decide) (by decide) (by decide) (by decide)

theorem prime_1871 : Nat.Prime 1871 := by
  let factors : List Nat := [2, 5, 11, 17]
  have hf : factors.prod = 1871 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_17, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (14 : ZMod 1871) ^ ((1871 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 1871) ^ ((1871 - 1) / 2) ≠ 1 from power_1871_2), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 1871) ^ ((1871 - 1) / 5) ≠ 1 from power_1871_5), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 1871) ^ ((1871 - 1) / 11) ≠ 1 from power_1871_11), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 1871) ^ ((1871 - 1) / 17) ≠ 1 from power_1871_17), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 1871 (14 : ZMod 1871) power_1871_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_1627771_full : List PowStep := [
  (1, 3),
  (8, 1501355),
  (13, 1491299),
  (6, 1372625),
  (7, 1504096),
  (10, 1)]

private theorem power_1627771_full : (3 : ZMod 1627771) ^ 1627770 = 1 :=
  trace_power 1627771 3 1627770 1 trace_1627771_full
    (by decide) (by decide) (by decide)

private def trace_1627771_2 : List PowStep := [
  (12, 531441),
  (6, 1510043),
  (11, 178913),
  (3, 61107),
  (13, 1627770)]

private theorem power_1627771_2 : (3 : ZMod 1627771) ^ 813885 ≠ 1 :=
  trace_power_ne_one 1627771 3 813885 1627770 trace_1627771_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_1627771_3 : List PowStep := [
  (8, 6561),
  (4, 1466485),
  (7, 1077685),
  (7, 1380353),
  (14, 1274054)]

private theorem power_1627771_3 : (3 : ZMod 1627771) ^ 542590 ≠ 1 :=
  trace_power_ne_one 1627771 3 542590 1274054 trace_1627771_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_1627771_5 : List PowStep := [
  (4, 81),
  (15, 698023),
  (7, 1166506),
  (11, 934630),
  (2, 528870)]

private theorem power_1627771_5 : (3 : ZMod 1627771) ^ 325554 ≠ 1 :=
  trace_power_ne_one 1627771 3 325554 528870 trace_1627771_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_1627771_29 : List PowStep := [
  (13, 1594323),
  (11, 240877),
  (4, 744710),
  (2, 366762)]

private theorem power_1627771_29 : (3 : ZMod 1627771) ^ 56130 ≠ 1 :=
  trace_power_ne_one 1627771 3 56130 366762 trace_1627771_29
    (by decide) (by decide) (by decide) (by decide)

private def trace_1627771_1871 : List PowStep := [
  (3, 27),
  (6, 306304),
  (6, 132478)]

private theorem power_1627771_1871 : (3 : ZMod 1627771) ^ 870 ≠ 1 :=
  trace_power_ne_one 1627771 3 870 132478 trace_1627771_1871
    (by decide) (by decide) (by decide) (by decide)

theorem prime_1627771 : Nat.Prime 1627771 := by
  let factors : List Nat := [2, 3, 5, 29, 1871]
  have hf : factors.prod = 1627771 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_29, (List.forall_mem_cons.mpr ⟨prime_1871, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 1627771) ^ ((1627771 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1627771) ^ ((1627771 - 1) / 2) ≠ 1 from power_1627771_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1627771) ^ ((1627771 - 1) / 3) ≠ 1 from power_1627771_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1627771) ^ ((1627771 - 1) / 5) ≠ 1 from power_1627771_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1627771) ^ ((1627771 - 1) / 29) ≠ 1 from power_1627771_29), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 1627771) ^ ((1627771 - 1) / 1871) ≠ 1 from power_1627771_1871), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 1627771 (3 : ZMod 1627771) power_1627771_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_297159362677_full : List PowStep := [
  (4, 16),
  (5, 226487423397),
  (3, 112290467293),
  (0, 123326844675),
  (1, 87916313685),
  (4, 79770855938),
  (0, 115839330943),
  (8, 174174378385),
  (7, 118472995023),
  (4, 1)]

private theorem power_297159362677_full : (2 : ZMod 297159362677) ^ 297159362676 = 1 :=
  trace_power 297159362677 2 297159362676 1 trace_297159362677_full
    (by decide) (by decide) (by decide)

private def trace_297159362677_2 : List PowStep := [
  (2, 4),
  (2, 17179869184),
  (9, 269658295859),
  (8, 74890879224),
  (0, 270826915561),
  (10, 290634715555),
  (0, 270275575767),
  (4, 243831331055),
  (3, 203784512581),
  (10, 297159362676)]

private theorem power_297159362677_2 : (2 : ZMod 297159362677) ^ 148579681338 ≠ 1 :=
  trace_power_ne_one 297159362677 2 148579681338 297159362676 trace_297159362677_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_297159362677_3 : List PowStep := [
  (1, 2),
  (7, 8388608),
  (1, 116182575377),
  (0, 49505451745),
  (0, 46757793871),
  (6, 145581729568),
  (10, 120160828249),
  (13, 161764481239),
  (7, 80095105930),
  (12, 21378871788)]

private theorem power_297159362677_3 : (2 : ZMod 297159362677) ^ 99053120892 ≠ 1 :=
  trace_power_ne_one 297159362677 2 99053120892 21378871788 trace_297159362677_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_297159362677_11 : List PowStep := [
  (6, 64),
  (4, 93547639683),
  (10, 280761385856),
  (3, 185464423333),
  (0, 191901726439),
  (5, 69959959725),
  (13, 41207344825),
  (13, 122535389976),
  (12, 235971553533)]

private theorem power_297159362677_11 : (2 : ZMod 297159362677) ^ 27014487516 ≠ 1 :=
  trace_power_ne_one 297159362677 2 27014487516 235971553533 trace_297159362677_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_297159362677_461 : List PowStep := [
  (2, 4),
  (6, 274877906944),
  (6, 113622228540),
  (11, 270138201379),
  (12, 227562059328),
  (6, 75738000364),
  (4, 111916174932),
  (4, 238970074943)]

private theorem power_297159362677_461 : (2 : ZMod 297159362677) ^ 644597316 ≠ 1 :=
  trace_power_ne_one 297159362677 2 644597316 238970074943 trace_297159362677_461
    (by decide) (by decide) (by decide) (by decide)

private def trace_297159362677_1627771 : List PowStep := [
  (2, 4),
  (12, 59783646473),
  (9, 11283931616),
  (1, 68510557173),
  (12, 114170894341)]

private theorem power_297159362677_1627771 : (2 : ZMod 297159362677) ^ 182556 ≠ 1 :=
  trace_power_ne_one 297159362677 2 182556 114170894341 trace_297159362677_1627771
    (by decide) (by decide) (by decide) (by decide)

theorem prime_297159362677 : Nat.Prime 297159362677 := by
  let factors : List Nat := [2, 2, 3, 3, 11, 461, 1627771]
  have hf : factors.prod = 297159362677 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_461, (List.forall_mem_cons.mpr ⟨prime_1627771, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 297159362677) ^ ((297159362677 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 297159362677) ^ ((297159362677 - 1) / 2) ≠ 1 from power_297159362677_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 297159362677) ^ ((297159362677 - 1) / 2) ≠ 1 from power_297159362677_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 297159362677) ^ ((297159362677 - 1) / 3) ≠ 1 from power_297159362677_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 297159362677) ^ ((297159362677 - 1) / 3) ≠ 1 from power_297159362677_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 297159362677) ^ ((297159362677 - 1) / 11) ≠ 1 from power_297159362677_11), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 297159362677) ^ ((297159362677 - 1) / 461) ≠ 1 from power_297159362677_461), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 297159362677) ^ ((297159362677 - 1) / 1627771) ≠ 1 from power_297159362677_1627771), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 297159362677 (2 : ZMod 297159362677) power_297159362677_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_29047611873442575647497758179_full : List PowStep := [
  (5, 32),
  (13, 9903520314283042199192993792),
  (13, 414163991802779441858569566),
  (11, 6077049811026848279743098956),
  (9, 16195036125962453534741903932),
  (15, 16296387088269987438946637188),
  (1, 14149285654214691480427753632),
  (2, 13150448658013224381482943965),
  (14, 18050688966128684316949468198),
  (15, 10863474341539861990442558073),
  (6, 18430457425924716701111221614),
  (3, 6406491872239841929871155185),
  (4, 6453900962253149128210863791),
  (8, 7463828837954533670646702346),
  (10, 9430457814759539731876994443),
  (3, 29044338730221774172262015148),
  (14, 14559126779120301807695479779),
  (2, 22064965758180881593104132717),
  (3, 15213365086759052191623485873),
  (11, 7519505381430136976249701944),
  (10, 26847469595005542104634408509),
  (5, 25726005236843945498966098008),
  (14, 13685076200711861086720360279),
  (2, 1)]

private theorem power_29047611873442575647497758179_full : (2 : ZMod 29047611873442575647497758179) ^ 29047611873442575647497758178 = 1 :=
  trace_power 29047611873442575647497758179 2 29047611873442575647497758178 1 trace_29047611873442575647497758179_full
    (by decide) (by decide) (by decide)

private def trace_29047611873442575647497758179_2 : List PowStep := [
  (2, 4),
  (14, 70368744177664),
  (14, 5278713481351150266587936635),
  (13, 25942584135935475305489371667),
  (12, 24337791434556870001527243069),
  (15, 21873230107705733815032118634),
  (8, 1547736195157547703154866172),
  (9, 1923892782130181998037627897),
  (7, 26608828849496614372069242598),
  (7, 21444639420703254445166966647),
  (11, 11852647346377338034779168176),
  (1, 21035296746156983522273039429),
  (10, 15395490422454412962560786995),
  (4, 20321198011284473331657389747),
  (5, 14455949047867561531216200364),
  (1, 20478791032545780821915042373),
  (15, 8501597987453685060780952696),
  (1, 25694676566488861367634463734),
  (1, 20302574171845068544607820060),
  (13, 994218313400367596445660245),
  (13, 20080337413008596044445778363),
  (2, 14008027081623247737352483589),
  (15, 7265325193771103054053855883),
  (1, 29047611873442575647497758178)]

private theorem power_29047611873442575647497758179_2 : (2 : ZMod 29047611873442575647497758179) ^ 14523805936721287823748879089 ≠ 1 :=
  trace_power_ne_one 29047611873442575647497758179 2 14523805936721287823748879089 29047611873442575647497758178 trace_29047611873442575647497758179_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_29047611873442575647497758179_293 : List PowStep := [
  (5, 32),
  (2, 4835703278458516698824704),
  (0, 26904331043832009584133638041),
  (1, 11446497360840292608389277158),
  (6, 2412415073881830348185145648),
  (10, 20173021633744399489319925042),
  (10, 27444387703321390637726559350),
  (8, 8970468731430248754857191658),
  (9, 3016326500089732744557063706),
  (2, 18447053400512388040994060763),
  (4, 842947681873494420226957880),
  (0, 3411833494435148370430830271),
  (0, 4076003284023215330566406712),
  (7, 7970788901884215612535644792),
  (8, 19966447486787263405140707780),
  (12, 24660785614444124591928821322),
  (9, 10645928770032898499114010266),
  (1, 13344652792412777367066384981),
  (3, 4192147254568316854385692550),
  (13, 657891052749488779363979993),
  (11, 21226009108094836760084484986),
  (10, 6256662822391641148461841119)]

private theorem power_29047611873442575647497758179_293 : (2 : ZMod 29047611873442575647497758179) ^ 99138607076595821322517946 ≠ 1 :=
  trace_power_ne_one 29047611873442575647497758179 2 99138607076595821322517946 6256662822391641148461841119 trace_29047611873442575647497758179_293
    (by decide) (by decide) (by decide) (by decide)

private def trace_29047611873442575647497758179_305873 : List PowStep := [
  (1, 2),
  (4, 1048576),
  (1, 6953714617026919963880896250),
  (12, 21516206581305756928913557946),
  (2, 24850771763733672093654370412),
  (1, 17546904358209808390047112791),
  (7, 14300149957428349446198300791),
  (8, 17411152074825072725888670676),
  (6, 10055397469548484241653383832),
  (9, 14151300764086030884238997487),
  (8, 10343986826739097975040424126),
  (1, 1100187039060748499112479497),
  (5, 5265846066114414059870143919),
  (1, 18303059029855700527446162782),
  (7, 24193144100821482210965226111),
  (12, 37129223178884370978126799),
  (13, 27520292025079946742251441981),
  (12, 19131957759735948501325334189),
  (4, 13713556653217369006003860553),
  (2, 15515419077790409984750505041)]

private theorem power_29047611873442575647497758179_305873 : (2 : ZMod 29047611873442575647497758179) ^ 94966250285061367454786 ≠ 1 :=
  trace_power_ne_one 29047611873442575647497758179 2 94966250285061367454786 15515419077790409984750505041 trace_29047611873442575647497758179_305873
    (by decide) (by decide) (by decide) (by decide)

private def trace_29047611873442575647497758179_545358713 : List PowStep := [
  (2, 4),
  (14, 70368744177664),
  (3, 16214208537512800349295178484),
  (2, 15729558174226985655492776657),
  (13, 16835673418916735718825672846),
  (4, 25390524568999473205642995374),
  (13, 11625086498601002292408050772),
  (0, 27892384614377972227795981583),
  (12, 3499544109220348539616714167),
  (6, 27080059527016500467855872482),
  (10, 22792286300598933841008949152),
  (5, 22004432619809156758284895662),
  (7, 13157392031377908459576887090),
  (6, 7894982977977529304551145808),
  (10, 18571018051465515423978504094),
  (7, 12721280599252849496323726351),
  (2, 1548700731856248688196814844)]

private theorem power_29047611873442575647497758179_545358713 : (2 : ZMod 29047611873442575647497758179) ^ 53263313083699784306 ≠ 1 :=
  trace_power_ne_one 29047611873442575647497758179 2 53263313083699784306 1548700731856248688196814844 trace_29047611873442575647497758179_545358713
    (by decide) (by decide) (by decide) (by decide)

private def trace_29047611873442575647497758179_297159362677 : List PowStep := [
  (1, 2),
  (5, 2097152),
  (11, 19973970749247333108955540126),
  (4, 1270051737333756921001822986),
  (7, 7192864591615979608794928656),
  (15, 7705964023916547322316539136),
  (10, 27569234257580178567110407306),
  (1, 21887652137949121524795926868),
  (2, 18144198785518112772489506428),
  (5, 2330960142250389514671842484),
  (14, 10780368566427290402812168186),
  (6, 6650056506411932292449235644),
  (2, 11594970534515685948366129868),
  (1, 19248229296938659176493019324),
  (10, 16062460713643416818883781819)]

private theorem power_29047611873442575647497758179_297159362677 : (2 : ZMod 29047611873442575647497758179) ^ 97750956294169114 ≠ 1 :=
  trace_power_ne_one 29047611873442575647497758179 2 97750956294169114 16062460713643416818883781819 trace_29047611873442575647497758179_297159362677
    (by decide) (by decide) (by decide) (by decide)

theorem prime_29047611873442575647497758179 : Nat.Prime 29047611873442575647497758179 := by
  let factors : List Nat := [2, 293, 305873, 545358713, 297159362677]
  have hf : factors.prod = 29047611873442575647497758179 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_293, (List.forall_mem_cons.mpr ⟨prime_305873, (List.forall_mem_cons.mpr ⟨prime_545358713, (List.forall_mem_cons.mpr ⟨prime_297159362677, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 29047611873442575647497758179) ^ ((29047611873442575647497758179 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 29047611873442575647497758179) ^ ((29047611873442575647497758179 - 1) / 2) ≠ 1 from power_29047611873442575647497758179_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 29047611873442575647497758179) ^ ((29047611873442575647497758179 - 1) / 293) ≠ 1 from power_29047611873442575647497758179_293), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 29047611873442575647497758179) ^ ((29047611873442575647497758179 - 1) / 305873) ≠ 1 from power_29047611873442575647497758179_305873), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 29047611873442575647497758179) ^ ((29047611873442575647497758179 - 1) / 545358713) ≠ 1 from power_29047611873442575647497758179_545358713), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 29047611873442575647497758179) ^ ((29047611873442575647497758179 - 1) / 297159362677) ≠ 1 from power_29047611873442575647497758179_297159362677), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 29047611873442575647497758179 (2 : ZMod 29047611873442575647497758179) power_29047611873442575647497758179_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_341948486974166000522343609283189_full : List PowStep := [
  (1, 2),
  (0, 65536),
  (13, 229585482569321192438453973412339),
  (11, 228883591106104795365880988370916),
  (15, 277315028019202026982638168736531),
  (15, 111717519018478728576913142804787),
  (2, 146420810388475641080550444117616),
  (6, 252094705891984548502831648554790),
  (14, 231305697941748694821345986643026),
  (10, 47111852021245812987075930089853),
  (11, 24518394638231744271948223185797),
  (8, 262850047149108010535611899968441),
  (1, 190524604269637192942615829625703),
  (9, 61633323458560313240110630729255),
  (8, 137517016224566798841487183353418),
  (0, 61263633878476768637669902432001),
  (5, 220322501110171565331264147131597),
  (0, 109281405480278211145439813635301),
  (1, 309013417285385126286757242920515),
  (7, 117499631572621151409007932188045),
  (2, 119487099651226208658619816380935),
  (14, 214212795492965773624511161474418),
  (14, 217930884518224390126660921902910),
  (0, 201098571625335741308211780738128),
  (3, 267178159625846624590809099385391),
  (2, 274649336938193163363693343647723),
  (7, 41793154875004443657427031582650),
  (4, 1)]

private theorem power_341948486974166000522343609283189_full : (2 : ZMod 341948486974166000522343609283189) ^ 341948486974166000522343609283188 = 1 :=
  trace_power 341948486974166000522343609283189 2 341948486974166000522343609283188 1 trace_341948486974166000522343609283189_full
    (by decide) (by decide) (by decide)

private def trace_341948486974166000522343609283189_2 : List PowStep := [
  (8, 256),
  (6, 164977513657164869423253502058188),
  (13, 260309830272677771389124044522179),
  (15, 210253268856166358603018721543123),
  (15, 253645848135047471417114352171291),
  (9, 27419274616636722560700867989538),
  (3, 30777976202958403434586032612447),
  (7, 111004212228871879958130676533318),
  (5, 35648116813762321675153444152971),
  (5, 147800726018391250254977370633900),
  (12, 329585464530993238512361729784515),
  (0, 194971259622502815733564824478634),
  (12, 202794101451069421840538304279126),
  (12, 322548883220282035818445794836560),
  (0, 182809738593229134358405758861414),
  (2, 31793571844232713571921641539192),
  (8, 330271878551463128884689462994773),
  (0, 255483051224720581141905483218464),
  (11, 164731868556957677321310605230867),
  (9, 171665306997138096933959328606565),
  (7, 147898201522062246460061641769719),
  (7, 319398792465551472116362242942311),
  (0, 223666510371679421879664187452038),
  (1, 8439513046090605120158346526537),
  (9, 147419783350882809704899121063882),
  (3, 33219114215390164422603822548148),
  (10, 341948486974166000522343609283188)]

private theorem power_341948486974166000522343609283189_2 : (2 : ZMod 341948486974166000522343609283189) ^ 170974243487083000261171804641594 ≠ 1 :=
  trace_power_ne_one 341948486974166000522343609283189 2 170974243487083000261171804641594 341948486974166000522343609283188 trace_341948486974166000522343609283189_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_341948486974166000522343609283189_3 : List PowStep := [
  (5, 32),
  (9, 618970019642690137449562112),
  (14, 245967559964326148885735235160011),
  (10, 172873645262516166845920507551008),
  (10, 72302019355055989282724709759287),
  (6, 167887125020111236020619174038068),
  (2, 326774331026901574490419053598873),
  (4, 270947499290859398058765573445215),
  (14, 224923974616627227971681222519132),
  (3, 159529986594704668286112044938133),
  (13, 264522290376816973673015314730878),
  (5, 20250346865108177122369869547741),
  (13, 61036352550938964894217463452290),
  (13, 127335351584859361717203609328999),
  (5, 327611356532897948045497841441568),
  (7, 223928552772314665159557937187246),
  (0, 60684126206272925803544698107275),
  (0, 2183895676390550668378617667974),
  (7, 41794936596974238967479551642445),
  (11, 251055398796906011694211154208212),
  (10, 134276550265737300920666604595145),
  (4, 14808045177413785197807769867127),
  (10, 148049919862183558715553436841013),
  (11, 228688069795951231469555278834897),
  (11, 56528674039094285287797788979616),
  (7, 204266139905929725829280164591237),
  (12, 165002932037550746596172898062794)]

private theorem power_341948486974166000522343609283189_3 : (2 : ZMod 341948486974166000522343609283189) ^ 113982828991388666840781203094396 ≠ 1 :=
  trace_power_ne_one 341948486974166000522343609283189 2 113982828991388666840781203094396 165002932037550746596172898062794 trace_341948486974166000522343609283189_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_341948486974166000522343609283189_109 : List PowStep := [
  (2, 4),
  (7, 549755813888),
  (9, 93557135418324039907276832808430),
  (8, 3784264490809988590343645035671),
  (10, 39752719184263741266520767350802),
  (7, 180677364577891055460785513919341),
  (1, 208938364372935602497443117769860),
  (11, 128867393527649291566221983797281),
  (15, 120720688359516790938652321980414),
  (12, 155634510410324851377363543629832),
  (15, 112784007824103242175103602467443),
  (13, 73118921788645636796742518190925),
  (14, 244784155566238157461138552878603),
  (2, 306538404686600973404659373273974),
  (10, 303513299469994481430928394220886),
  (5, 335845087882218147552700382596335),
  (2, 36749437145802249999607920266765),
  (3, 4864469842044160893935721980681),
  (7, 294291758912787188058327136922841),
  (1, 1499672454157198427312015293869),
  (2, 323320458092847574524778077796580),
  (9, 197855146531676424493697160748202),
  (15, 145660704059191231321802894185049),
  (11, 264372419817371859279064206588911),
  (12, 164993751097015892980557476442611),
  (4, 153618737808983370202320649387857)]

private theorem power_341948486974166000522343609283189_109 : (2 : ZMod 341948486974166000522343609283189) ^ 3137142082331798169929757883332 ≠ 1 :=
  trace_power_ne_one 341948486974166000522343609283189 2 3137142082331798169929757883332 153618737808983370202320649387857 trace_341948486974166000522343609283189_109
    (by decide) (by decide) (by decide) (by decide)

private def trace_341948486974166000522343609283189_29047611873442575647497758179 : List PowStep := [
  (2, 4),
  (13, 35184372088832),
  (15, 49588214830345929388481393163835),
  (12, 291782875431971620014836968593543)]

private theorem power_341948486974166000522343609283189_29047611873442575647497758179 : (2 : ZMod 341948486974166000522343609283189) ^ 11772 ≠ 1 :=
  trace_power_ne_one 341948486974166000522343609283189 2 11772 291782875431971620014836968593543 trace_341948486974166000522343609283189_29047611873442575647497758179
    (by decide) (by decide) (by decide) (by decide)

theorem prime_341948486974166000522343609283189 : Nat.Prime 341948486974166000522343609283189 := by
  let factors : List Nat := [2, 2, 3, 3, 3, 109, 29047611873442575647497758179]
  have hf : factors.prod = 341948486974166000522343609283189 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_109, (List.forall_mem_cons.mpr ⟨prime_29047611873442575647497758179, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 341948486974166000522343609283189) ^ ((341948486974166000522343609283189 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 341948486974166000522343609283189) ^ ((341948486974166000522343609283189 - 1) / 2) ≠ 1 from power_341948486974166000522343609283189_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 341948486974166000522343609283189) ^ ((341948486974166000522343609283189 - 1) / 2) ≠ 1 from power_341948486974166000522343609283189_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 341948486974166000522343609283189) ^ ((341948486974166000522343609283189 - 1) / 3) ≠ 1 from power_341948486974166000522343609283189_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 341948486974166000522343609283189) ^ ((341948486974166000522343609283189 - 1) / 3) ≠ 1 from power_341948486974166000522343609283189_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 341948486974166000522343609283189) ^ ((341948486974166000522343609283189 - 1) / 3) ≠ 1 from power_341948486974166000522343609283189_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 341948486974166000522343609283189) ^ ((341948486974166000522343609283189 - 1) / 109) ≠ 1 from power_341948486974166000522343609283189_109), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 341948486974166000522343609283189) ^ ((341948486974166000522343609283189 - 1) / 29047611873442575647497758179) ≠ 1 from power_341948486974166000522343609283189_29047611873442575647497758179), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 341948486974166000522343609283189 (2 : ZMod 341948486974166000522343609283189) power_341948486974166000522343609283189_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_full : List PowStep := [
  (15, 4747561509943),
  (15, 77172505014320580510840957671510811498014347110586537301274303426553851228920),
  (15, 57011003283804965736005257771715245604278431613243438616667213549308357145135),
  (15, 12456742950909188806225574182827515269518441889794886124032397225466302676527),
  (15, 102281146014980226467504105049773999300745936019666829588787549290786324995464),
  (15, 54691366977165956116952022802948357418877930408499528272384887372088685126355),
  (15, 18791313043937937811419553445196967030967437026654592032152784139050652170308),
  (15, 93272989258461853299900170294985451658632654035535809440599929410764567892994),
  (15, 29897141289796844814941062965237201362685163374594750981886131212222371724485),
  (15, 94656566543316332932919649996798985498463990723717870594583039401920359839152),
  (15, 111815713082010526488289952750371061262712230460463659837536642388204409246893),
  (15, 20487567174461711830421119676117839849596149199279008101470890661033516309752),
  (15, 110213559079708938211035191458406606856483462138091050439923202565160708421265),
  (15, 95075435171141603694018766745020791134203448356228999887320318731980836695973),
  (15, 80046609193677233145311348746949135457552687899093801525687033367695292728898),
  (15, 110124638440727196711655606609206803909959691034542478324067601516175391091377),
  (15, 25424063828192308345495421686240998955508216744976727501337444972244226574568),
  (15, 108865295264660799562860233525874768382044598885838613552516575964539871511776),
  (15, 89785336299801072679454681298056402857477779902608567955835888070830629582297),
  (15, 82192388170629934419124153033187371064262145505197548809529974096341044721503),
  (15, 81340706400409285125533488294821915232858115174453601562598663005260031319334),
  (15, 48204077189222570569219171066883070323251442086049561197357432268581344752349),
  (15, 70465251722200329054362911053460830599489307804360773507620972360178614312458),
  (15, 86412573864819924452464910997543709957087346532299033682380820667188779150542),
  (15, 46851953713398940632254143126714289947798683970637435156100283786792880892386),
  (15, 37337857184291784822222488147966675148845967148861641161430789802920518690753),
  (15, 40505021066252045321114932213326722973839723434225082072964476125216521474382),
  (15, 74422741845608630768981795736702469182547604209133904038312185464524287996740),
  (15, 23035303298110660219504990964117739999998370705897504934437084198844255290554),
  (15, 33076593345697787244568677378555455219402657175737946949041459091508321497286),
  (15, 84295363352212492804510891019634186459280865063445401376630056212371133458626),
  (14, 18003629927241428492691071931786963783052768749517431256045055220127620157256),
  (11, 66631477429750099372587873464645250541223079393654921567336203373251292817241),
  (10, 87793215280803410919219297818411113957223885121669485022906308607839922256699),
  (10, 7036957809350230453957911732901544058301389273641038940297631306536248470180),
  (14, 31467659564008360479560143334566498602357894934138406559606953726507259261708),
  (13, 26909662852920858881746777534748643629534148932731663199424546199886273326614),
  (12, 23342148161073995599945703140314535269627307472848712463352122229148886880307),
  (14, 74265792724627850123759334847607529755703015688135857553174245982527015230704),
  (6, 109230224676230546768001754547101870683104701906944239409824506651117350184492),
  (10, 29997424789964975370824223701538562865238575606058649665838838558475499260504),
  (15, 76774792326459022900364657141709223349887364562123000499342501832626156669860),
  (4, 69044232131248576090237918983575807970640797335866988155197940605815948828982),
  (8, 92096285214110652439957477793337049900701392424498672991457789833843999811994),
  (10, 97205195297088324687368651844682984422160610111973538630213832845032609879730),
  (0, 32203960657969418778990118720552485852667208511340370487599776192293356149083),
  (3, 44464119431005709639639032744515708688111487063131105402280497574359161975957),
  (11, 113475810502447261375580410284741787604286136617180782689446508823260498894078),
  (11, 16013235898037052763191348417141865919797850836275891603787764151444764717025),
  (15, 79669216353922436965149098154647537759450196302949176340872764162746710348574),
  (13, 70963385391693156680738985423895276974093862737578584219268576228578396070992),
  (2, 96883194691722398541161438231992224992614645913739982631524068013082663362765),
  (5, 102835131402223926846930872513846888759344099660233603358150441182469729803763),
  (14, 98328502457745853069364325736182143181572909355534301815804509084745111747575),
  (8, 1458271808670284976690266146474297153274981496165395703534508942339134205623),
  (12, 51491477161806955124811281713566427332610084564897558486299429641386378390618),
  (13, 88098289929922166099507153964549814917540519846660221761728314354878666270331),
  (0, 57422004350320737271730697662073176454057261003911607880829124269607003872515),
  (3, 53976209834892222266114654956916863143159123353875250357054298788913452681269),
  (6, 27370025733480021374754828281390848172440105247471736596729995588513104882172),
  (4, 2703427642427110268622546595704787856377460059155141255780765410855367645133),
  (1, 101886153939491735783664044613336464995804935626696159040104800521251599711824),
  (4, 96392582047544156033893756239406269239864930626642284691348847098609918088905),
  (0, 1)]

private theorem power_115792089237316195423570985008687907852837564279074904382605163141518161494337_full : (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ 115792089237316195423570985008687907852837564279074904382605163141518161494336 = 1 :=
  trace_power 115792089237316195423570985008687907852837564279074904382605163141518161494337 7 115792089237316195423570985008687907852837564279074904382605163141518161494336 1 trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_full
    (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_2 : List PowStep := [
  (7, 823543),
  (15, 32294996771478358890215435346032669555297979646695501412545532459080382085999),
  (15, 64878312710543373960607171836387912299926514903848221506087876258371953283367),
  (15, 44846168704780327416085757332131438140129546679502266520876575338454288483218),
  (15, 67743352574782990195512511560917013173258353063800537763962800035196605827426),
  (15, 67981927534198214058531338796707017026179012327453225770866100411718645980342),
  (15, 62627453272020581602043480076394671564560049039718726420537678952887214717548),
  (15, 23904010671869998306430499920648452672277980206870336600628602428554689812279),
  (15, 55615794236858639300209734174373157437226233204877997588657673795442513864072),
  (15, 16119406213138332914742400665701888908257415149211070933727676225492555159204),
  (15, 33838385411855477835468267850923594370640203842777228669426612258931033249495),
  (15, 100629217566626272088605622388034903638341494292993284056558034430427038550777),
  (15, 107782323371716182413926241782897046552228031195895408439492824814083356860120),
  (15, 49864902580096407228676531782073978646061554675382580433294665437110713840511),
  (15, 98334548196192881245114387084555187637555505772690584904980930908912683850474),
  (15, 18133977712387949693529057609218333571975248545563825434792128001491110110664),
  (15, 100780804843909887665956127100468879851536212163313205896461502754203196326985),
  (15, 104628885173480434864583346144949378343709226585136944189171352624366815273286),
  (15, 49978173413646590083934832251577563781269483008243852160521556705445037878653),
  (15, 39682624958608880947388577471284405189211364592450905514187305555737714573954),
  (15, 64809221196355006952272074208976957452086859005497854846988669746351403809121),
  (15, 97681727853800142927185415386905384063261778061613415119010155418725499782278),
  (15, 47941158788930042418652929961064652021024644589083883832204133279907741573108),
  (15, 45046196188489285321396783335504538953680076996773338146948270877642220538488),
  (15, 97817049969364562333566636868185799925660491380298895756288761842433014611166),
  (15, 62366556630363313092756410437466813842898698009568191164641613048127233262380),
  (15, 17271464635538474817102698908953427979182801784017567819014120822110071698062),
  (15, 9901549858376741887314998847770988494455836171701317280282399899607763119417),
  (15, 26105393364156070936440976078487370482383920472296055728908826168747292571407),
  (15, 105762427657170775369545611437563928863384724548810468717138243123409482043704),
  (15, 74548721196240097349623498619041524701316452148402353463236034771629097194213),
  (15, 47034610554653992026849010554241048494034199791874084080163723477316731755346),
  (5, 61336615770906186115805580597490213458957303033237680109769962214282091057733),
  (13, 712072615703304725088457827425274250801612082876045692221409466354960395668),
  (5, 22707004687399886941290367490415043823671688053743517961029396866246140495422),
  (7, 38891269544415659050825688080557030249249148855764888474183726831886623211424),
  (6, 27772181542829693641973458366731126067048322304229120964095066500686892192489),
  (14, 71651043480833000587203666768098938906753336256335609421283701989484231045335),
  (7, 50613314087166976901971093900349647239269223855804664056704354477051840731004),
  (3, 17955656864041465038025328074916808325918760689232796790033063659663294167810),
  (5, 49678187227387188956904581393146552011855716952125270011661976153730300658937),
  (7, 39158480669065287271940438195478184709532707777814764077017658337316006823504),
  (10, 71792585527974958748741433195300079733192459197915041587335834998840486231210),
  (4, 113946736726409621394637229134583198356823519821899758825310690171842681116187),
  (5, 76744189921184481252082104648807944699277997868486130728980993277666239920025),
  (0, 53446992753899416470965206052201951680184211166560933731288669423439037462270),
  (1, 17999927201533125123979370329377484794781490806295890171531137341626946117542),
  (13, 87063347248510372923666481993875452986097634012554613973482476439613918238876),
  (13, 48892756719082451739094694727189752592535703337007929567222670036757210875234),
  (15, 63520909428125643116968676146081375979669641112018230624882831326458153184768),
  (14, 99470361167844311357576743069196944105908521167461121586169830635510991467427),
  (9, 27241881881781669992096413550711635122472245506350184067123990851420288542167),
  (2, 51267511075487682868441360852372856408071512996068231961210124101685109756863),
  (15, 48287684597602232364818278729841788731178935739793444824425462145414003849133),
  (4, 59847336432787086580552035338806856671421596002232423124241744803308142208472),
  (6, 111339545027181065397120753185158946872784332279142214960763029584757046346950),
  (6, 84516193209534506793895470714997118215456852087363962241487193787281957757743),
  (8, 100015650921944566261201376547646461863114245465152026530196214425501801373917),
  (1, 26345065443854858697161834852577122404744684718137955962099631736327411515650),
  (11, 90068968412395998721199831672200330906706867405615133944793311498077466594116),
  (2, 34875893598712827977072526201502948442506284428936811000969358722022152880810),
  (0, 42168705040770636958721412192139204187205331584370833096162539961416409146541),
  (10, 15363223041448804065593189986566810604650548223542378610511887785282605389003),
  (0, 115792089237316195423570985008687907852837564279074904382605163141518161494336)]

private theorem power_115792089237316195423570985008687907852837564279074904382605163141518161494337_2 : (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ 57896044618658097711785492504343953926418782139537452191302581570759080747168 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907852837564279074904382605163141518161494337 7 57896044618658097711785492504343953926418782139537452191302581570759080747168 115792089237316195423570985008687907852837564279074904382605163141518161494336 trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_3 : List PowStep := [
  (5, 16807),
  (5, 681292175541205709486531011694243236571309860372760091522256581907552807),
  (5, 95078170650825756182899689178493468624164862706108223338156670371209201668164),
  (5, 61623419387916213965434426105539164535304848746142312864700674596706153180126),
  (5, 81498721660224469394260671887046968654461377432154450924367430661391721754753),
  (5, 67840449359482366100405544577660726586716377871692767415787395484407816063587),
  (5, 33841179317736694324000568429134385491602353915521931368682925961528967937480),
  (5, 5669899968255311862123142004939749046664634953476531116348417352267553735018),
  (5, 90537862592045041244992620530712190716318428805311128948336357912147917877854),
  (5, 107768382089958739267803262433268362703433838023061235072826867247130134666905),
  (5, 94482150135370398150389878005664840403425279922885609928949125088720143984490),
  (5, 102115121891375745947865108226719766057150201614250536494515888176491480309164),
  (5, 109941839889923113757673396787335694657590576313120881099879987914597048086381),
  (5, 93808978432235175698013687317517104477546909294375460395725611115928184708426),
  (5, 69102552672746101222535506307083407980095978098966060411860899979937969797860),
  (5, 106630706315885989283175421251516752507798545709779562501279973000472524504124),
  (5, 78501784395090154635795149093281675899544479236715159135806139055055245193287),
  (5, 97719290177817932673906081568727542760615363905770899952817655864391566601640),
  (5, 86587767289599242969741987590496558411951956616611063075279211816940091019547),
  (5, 12270189658499352240401670534973148965567024139938123392787872583227554952124),
  (5, 56664979164128227150312851683714840185002409008377050689705345855547893283516),
  (5, 38259911194560612812165187044888514502136645694025397994412388070985517763768),
  (5, 72261816167972999713632949062286202613852509627973629640613086132128145755151),
  (5, 82303200676870729431983171729781861236383110386974579672113725425651876616261),
  (5, 488712247564347630439920836000630929775862524684303280629807192607763926713),
  (5, 32020886963726211963685353807420871722652834502064226375578238090888348680203),
  (5, 57206680491344407544702771115818692611530144093190579599588446482015929402981),
  (5, 36814892963733406024406879857222040566523065874637663988317243433097535384278),
  (5, 113052887970220175011949818293794300929263690037725167049886948011366753571881),
  (5, 10935840998209443612774291623550336281793101815554301518789943628952616234983),
  (5, 15067707790135227144508000342750498019227934552769164537991473672711927204986),
  (4, 67986583321797317001708620588982780469908420467814517391999798748188715807058),
  (14, 76602500506150737453392177454559178956331874506124221014683554345166410675131),
  (8, 94279035149598714543439099163054576226943710548335117831583077245918404726581),
  (14, 12168621948107239143704337134615334466616255896897134244186668257596169405150),
  (4, 40032671319612230252382760628567625818774069284501092208140884052461099023410),
  (15, 20029696250614114540841559055244763339388921236433383565175654452660667080072),
  (4, 61694982065798486468260446580688133020557539401211610279949613352418153802191),
  (4, 40429852539095919969144830864698550312802910109218640317880063135866544825595),
  (12, 106014187212467970268624185119728248495726313618695897575778352947422047935419),
  (14, 77042181664681967738593404356208127547887848321649143213204962053678538517543),
  (5, 80077419413296187845804542214252275153161131194701121292128251689111186228141),
  (1, 40115115260007274437494109178622171842092180913735310996659873196301631587431),
  (8, 69970515535954223165340134831305273128116901476233517089285478781114687859974),
  (3, 51196746959945633838676324534212668978974183616794250950623139718056302190922),
  (5, 113394678362085573821328353010723229469306232238441963442807203362114730072411),
  (6, 62122950001922934214828808416385053222505218018069622772566871515434622621783),
  (9, 8478593996714791392948727151746349438456559690961072729202899363590636034781),
  (3, 106098572455151050169831941615439789307176370117046869591081225898781245074396),
  (15, 36486759925937863843657442072850104597682101251946374444423439355516954803583),
  (15, 7111681348408055550208899159727674658961216374163619087632344858736195492239),
  (0, 67407559948492148842116116108910883830869996448939903186950150465737833448524),
  (12, 111949009835130837635060683391416311246203603538159397622403947225961445779945),
  (10, 63434962990775232105485377207239976373133448688548933569584135438822580351572),
  (2, 38032061647817426366282551024123447913282817817784451398869775635018929898197),
  (14, 12785348043570313468546542533453369040030662975519642665412101097194466784074),
  (15, 75263150491982375397758960506575304312120395805620794218179489479958779769792),
  (0, 52970620941113949439337869590025164075134606710201104498780193992505530203168),
  (1, 44685691015417757960739755089868481199590384186839679275808467336971507361634),
  (2, 28568110463863084741128867537214121210211884765842141840246892091029473855033),
  (1, 45025308403511314852975925485499198089243684039570066834269301791746407295579),
  (5, 15942062685414953036468369555797676959303364128479731385758234085359255276490),
  (12, 52650891648782711747567863454529138043732571163910658920148800246585903856232),
  (0, 78074008874160198520644763525212887401909906723592317393988542598630163514318)]

private theorem power_115792089237316195423570985008687907852837564279074904382605163141518161494337_3 : (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ 38597363079105398474523661669562635950945854759691634794201721047172720498112 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907852837564279074904382605163141518161494337 7 38597363079105398474523661669562635950945854759691634794201721047172720498112 78074008874160198520644763525212887401909906723592317393988542598630163514318 trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_149 : List PowStep := [
  (1, 7),
  (11, 65712362363534280139543),
  (7, 56695299109034402837544649983654313640038622017510135941622995617275942776901),
  (13, 25100558890163373810648319806856917921485814516299837067312800433972457219336),
  (6, 113925959915287592203335507580029992093724791092832682939671964113424830992756),
  (12, 64425390003504787773635003547101123783520745316813178803128909896377733728644),
  (3, 96036563931351057484477226026787475087240915197850349519750121287483614005815),
  (13, 40652524178721924018745961971296486461888499059470285869723614140886333516724),
  (13, 89144167656383740577229317297802036878835324723177922672615495304507456572679),
  (10, 115501387167030984508224024810421657546025882039475099253232798324941793887278),
  (3, 9918033534337426466527585798553953144510250693190419251886657813660481161426),
  (3, 5406207667442923716659620964045526059313924637447626308153648892160806062958),
  (8, 54454025033034296506405746389600488574264862654487452062602726721211571587921),
  (11, 98174866405656809981987454769479688983571138479706601717863164905969212000990),
  (2, 78375578727403407109598984922101668404040012571081323375392131051177582357724),
  (10, 92450502825786861987233114081201496610096763515417138979229263292820483255503),
  (15, 53400359696947042242954413905621353217206294189947205663604449185353684907697),
  (3, 99345852967531372554559004962202955952026725295615199728275117287414508974092),
  (15, 36220932321574895289223034133237230910923815696528078947700404056197983446467),
  (9, 14849529274476513423971125533865470584302513728825753789224572949928098281905),
  (2, 46502499081832317404833217368542926510065529921778970370359696148604910530152),
  (0, 24923971609122953529412418121007214021561648197333435418041559188999915212880),
  (10, 85882425718001034195642492358968590299483768582591500462742248786911780249182),
  (4, 11528594338761691172267633372483190759445365063536029826788123719882581236276),
  (15, 82162606167708444923998419993231291040722693936949921224268247214927099163504),
  (0, 17858635114849756029946082396509393099843908935298650387741723206546616427033),
  (8, 93121911560254646260066221101227781924169577748909012439253946910763295165811),
  (9, 103194082771674941377062258271825186674337405085434361339482080873336730232436),
  (7, 4646814057619104858561050744327090613466718913860642175032208593748305685098),
  (3, 29249743141569592645078698539617516420874791394893046660192377675282614894252),
  (1, 11502185002355350422632197881402102076664309920363744743034920124229393581670),
  (13, 108165265498957646553817733699553104800001162201982501693514710752853082056654),
  (1, 90006684159544370195603561871769550878925641295796237021185540574965311705925),
  (2, 101175530045562825443506529624085371053207655819601476566547168120659001846402),
  (5, 10822298485836804717408173775298166349298109716444299545605052298998726427174),
  (4, 89999518734977255862651672527730584211859583956001586779250574867708011275239),
  (1, 66260259342000229507237139797172182596580200777115547126348658065150595331110),
  (0, 15265724489608654799860788617657769614205933189507562173249467451196967018706),
  (13, 39418667579767717714669538754282057392664738204995385466416838978875953184610),
  (9, 38268282978870212389934258502331189786923802778092495603003137618599149200035),
  (3, 105470340737911187492748057041864041925242233438985629759087698191000074434117),
  (3, 29024744779828665860768001608090011771164140389930646681800314590229953602407),
  (7, 26448646492981199197990278960565897006822820364516950581901306245958213404711),
  (7, 67228024119774332175772285768843782762908763427161578726349577078681644248808),
  (7, 42844165400066951788308553112543791538380245524905868201380730208902323059587),
  (10, 20293630502287223977769204165738151435058518263385106328292773222227540205335),
  (0, 13291901505188506002452243938122669341397167020954981228622181592679087784159),
  (2, 71407622788779470170128287691517086701333655256871275464104958373434839267165),
  (15, 17857258513456322241496971120558809554716762053224381590358437379875777029222),
  (10, 74682643019299045186016581427820662078137855874141618572709193225800337666678),
  (13, 48246611499749639679542510422962705042838141658081270082349948321633597486566),
  (3, 46460856474211263431522282898476654130272756694200414774534339096107372568617),
  (9, 109174095222375716158930940428467010780848137654095438658528552126204621448801),
  (5, 85492593664512081603744707614889628880417478331267852827574372790684857442284),
  (5, 106201717058313228991846134112524236836722489357230225525713899953492832387054),
  (2, 91590790790415714023783687471003026170821192134500723781711457936719907587720),
  (2, 5606412907346621597348351340692537977005853943443207463917658277541450523522),
  (0, 65514789318903971875200072002438539803445934252419970110456698589480511924889),
  (10, 41161065321430876961036171677317166524366351185058324707209888311423904203022),
  (10, 81979984184024193507765392040005695939558220460951936319846879553268732209649),
  (12, 110879945933381910250301819258579322506068249061862506444929277588975874657923),
  (4, 44621612386240364492131679115492858176121259656988183941366753020945208578490),
  (0, 64883128911135277911836602334573374963230868236696644030005288079353585574111)]

private theorem power_115792089237316195423570985008687907852837564279074904382605163141518161494337_149 : (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ 777128115686685875325979765158979247334480297174999358272517873433007795264 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907852837564279074904382605163141518161494337 7 777128115686685875325979765158979247334480297174999358272517873433007795264 64883128911135277911836602334573374963230868236696644030005288079353585574111 trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_149
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_631 : List PowStep := [
  (6, 117649),
  (7, 39629642991935179701677757654418553018057818447062009592848418111613211431892),
  (13, 94107276890783028882969423187602375726671241578358814905484559721321967703236),
  (12, 21743932496687692253917985243350086581453583035027073387937656630531014352831),
  (4, 71154604503095449715991246719611510345344550848919201606066726868289187792614),
  (12, 84117677031809284439011533530325714776467693340418670442350316883860950893076),
  (4, 110345982627429970056763820241304466248019374861977701212862672086865273346862),
  (5, 90953682935910237475399369855611332508247167752704222681916760654097142509548),
  (12, 9565953237635410646124243763888787160833793356735394972244111987595845211936),
  (8, 79275419392650810841211894089872197178339506629233505442409629427451728530519),
  (0, 96130366441039445502159681496720384925894203419145839200648273442251149920965),
  (3, 45573506035865828886936573496956650023514382577394761153206258472594456044372),
  (3, 12145558685801887763634184042082481873137935355268591587061360741895728720003),
  (14, 79741877407119781085312724461137359010072213017526367974138853152889839961886),
  (14, 60112037912517345513210772516579940298750181048469083344849284151449307871615),
  (2, 59187586903707613190436899117836721577867682400027962999355008413447950720471),
  (6, 47292567108441202522858434114784908221480727045423460821689746076331474663051),
  (2, 62061368843964025210302760028938820393260314812031759707133221192604863178158),
  (2, 57544387273353371916754518127983761810783686474376426508980308814908319463112),
  (14, 113268508247998485318617893810164518315793744118257271600967282761603928611393),
  (4, 45823453861770759355830110141705756807023167356356310587835208177462373761049),
  (0, 11293251073766617691110782955295454091756765584033006199948316676587851228700),
  (1, 49889923533207640757292339790682909807476605477634096310391131313304978823250),
  (9, 114877714209346077675046967916466257855500161093645930337739939576642175487774),
  (15, 17621816738862166345140313267587644764564166957419510858385907076151411892321),
  (7, 48752027213826373381165539572373584785811901337843345677061042872716127571078),
  (1, 57129418836897669721355950812304559005869691834803484228764871425648399136083),
  (3, 101153815665199682700347107637728726403960099411082013550297352808860412359298),
  (1, 94578583757837749144777970956141678382463835883213425686397464894368658445052),
  (1, 10682858615419256408150722688145713929831526294082116519025498053500972199932),
  (7, 3442585926058095503391315140045894238219602368565060854381752949960472687957),
  (1, 1482828866007547592919821841187001983241685946851255771601392084592760051670),
  (7, 42316108262738468171959629616858907232512491848468896763902398925057622396691),
  (12, 13889929820719708647108953117918410991794674553234540947752209461791995448610),
  (13, 9886787105446777929514747182627612972405697842852103709459549180972437996953),
  (4, 48527804645373574823177032323942869358026787470882128386086696028329132189496),
  (2, 106558507591058077624091369189310634902238237972098418810949254247645077939050),
  (0, 11485535857333305852854247626602887763189147995324473068386762870690540617888),
  (13, 93066646383748332749767798669409386761343380582944363928186111027802196826438),
  (2, 109414842672193124710108077399314324818636700319430191026209612000235823425009),
  (6, 101237619980137477008101596614091216472232717080674002714401995164599236165781),
  (14, 102126089886970452042683926028882481042418068853868439021642314295936309605561),
  (13, 44060344958675687056003317016235895762750048622221461056423825371066707904819),
  (15, 74713822048727034153495605175946215904973295802636362732244222669347564222478),
  (6, 113519678728518527745458378945764455636902373941376375830387296224339460650246),
  (4, 8144875509666013524162481076864081127143416461386392899840738617318773013495),
  (4, 49905475620786928819891556247623304228438823391820390078277546552169144343992),
  (13, 28472020919063237815381958859914136773891763380679420249650235649475755561696),
  (12, 12117587292616512063324106397094696663677321258233106369021655777734381926785),
  (11, 871603277964064332698134324893451016008751678294668016792488933282494821064),
  (2, 79739747869714803178638009367373912333081335018203687079408306861317398426698),
  (15, 50738362484812322522705364678683732316312971199599128792206832106221517635064),
  (9, 6902744527268384511912051631029542919173002870380886892256609173472535105794),
  (14, 59095505006586918371600419612529093636623765813576611001332120120825109671993),
  (0, 115119388902774139056578493641382630258588086211249730126507161517144851409715),
  (10, 5915023671200741009546923305162220469110438132999838498348977671703297677607),
  (14, 4675439199352519641687464866003866114139194211803601244298913379260669850460),
  (0, 66183071946602186961992889299013716547856702483967394617426341924874898041250),
  (13, 18277685746565859634604686957188643101359654544481099426313562703100255965229),
  (8, 71224905663572897227548648663469073813659860584297307991064271240401578548419),
  (12, 25808654490746525429047119939376960238951285673317305455259035529609112357161),
  (0, 6252150074946714737332729428705675642972902278047830378127425501959375813903)]

private theorem power_115792089237316195423570985008687907852837564279074904382605163141518161494337_631 : (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ 183505688173242781970793954054972912603546060664144063997789481999236389056 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907852837564279074904382605163141518161494337 7 183505688173242781970793954054972912603546060664144063997789481999236389056 6252150074946714737332729428705675642972902278047830378127425501959375813903 trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_631
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_107361793816595537 : List PowStep := [
  (10, 282475249),
  (11, 104951470337401539059410962458686965351686674272499545740175683038443879464010),
  (13, 9684437507362110669380228053483072731805738682196215641522810838678706619758),
  (1, 42534949408761430196347531128542929929442294807512801265717167301684411656138),
  (8, 5651951135481308554326279173628361208915218710419681539515462661202275620935),
  (10, 57583829083559252252704125774308094153845290483098496479209937807501421587849),
  (4, 29487450463797939645873459555649117174296223423089659331758922927463530438116),
  (1, 51450034105433365704241855620818580189762598358913749889198037469444927136152),
  (6, 16397632823784326483256368778767898884293213320104352410943040845497033595328),
  (4, 52178994062015367534157408717528871402287581224318541206552260039391799581624),
  (15, 12626788457101449983436716853101017576210699256545858884592111558644168552662),
  (2, 71403506880593991363348155167394486494623541974470650360788284627658558933020),
  (14, 25758230099402264820848635345104067277438371599821426866555783165836339725283),
  (12, 12980374022813378685548770092634361543773596876171272549481710912903388798531),
  (2, 101784901947327496641814592192529252009257752556452763614750920687907520253869),
  (11, 76461102146508263534196958119710902064261574055612656731206374506047721027128),
  (4, 74054502445052555045002347734262537346873913863652712557988641804682844920648),
  (9, 16837633973200959061206601599797246520456697870087872404506711205006354404326),
  (15, 39544731616787683378189243353122783802121617582371942398517908701642334488262),
  (12, 23353961967023852421040151604791345777590126946219245757100851618405905998951),
  (5, 85400358188333870044505279226750863445966931854164821553577414894251716705847),
  (0, 64950004440704978648773599079341052411371974215301990098321708724391865465684),
  (12, 2060820153779832986945492790377265739520262477541384228374169822994274132582),
  (13, 41401763557914426840698200686098541123337395590095417832979786181555500919095),
  (11, 95377116497235685796404883932138383776664354781660468688899272204206332636647),
  (7, 33739169066292984711580711672628518956063284737604632676088874599532960786475),
  (14, 31721319610610617270638911460533206101144731878804186002486634533712622521971),
  (2, 52319408904153015506550866332092869457004003989144336771028707369231499279731),
  (7, 42311231429127954061578116403527012122023822721875521659177333276953311925608),
  (0, 72627564322351343792316624937990217971698961965386883514059359467426317747670),
  (5, 84776550326900410191463356345603971801278174751539034167211871868552880073509),
  (4, 21217565730312274833365853513319103354325466261325069707098697184155416030717),
  (2, 39116542351237265736761997245585655062540544600318091764538508316729503727574),
  (15, 106143191105814437518915540245544884808945126567226824849788761638778262698563),
  (2, 39374259121134253988373915634382157862106714915082743924274966319268565542905),
  (5, 33613433319279010987843156561797381365314100893972972243782497659577809327494),
  (6, 75638323680794887514586959394933874335953177512087000974203783445277821511775),
  (0, 27392568121251854784975057808317466224015042734100008571113519266842392656798),
  (10, 2730342440681740167392128070839191099484605441355654139301023025685913601986),
  (0, 69430853716400967014297200389416799500240126543227293821358254627686964161698),
  (15, 58633471801883433412071131046288668255595495693492831524031009207697934979775),
  (7, 18772065146649120000238017895779941963316405854405694602256585557864574769532),
  (0, 27778299380340859915392271790967496786822152320832574554780405757201019110828),
  (0, 5748834668842975448349123213234374880720221667525902516739615551826864922655),
  (10, 65351405770385559485646509308579970788284914536509065917058283529755049220995),
  (14, 99366253976287699369513216603431294251183084985622323608039841818474404094372),
  (1, 26224542016879870448703343630991995332666957867175424088765326957423689965813),
  (13, 11959301699841742761547191183513098198546157339417344943859076779630397532154),
  (4, 26776447000522013556877019482407218394344386847409796345401480787626589090571),
  (0, 26709443456820378470009624069039436105476083851490662296256974102742433182582)]

private theorem power_115792089237316195423570985008687907852837564279074904382605163141518161494337_107361793816595537 : (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ 1078522304080742162682399010554089082520748534743704783428928 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907852837564279074904382605163141518161494337 7 1078522304080742162682399010554089082520748534743704783428928 26709443456820378470009624069039436105476083851490662296256974102742433182582 trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_107361793816595537
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_174723607534414371449 : List PowStep := [
  (1, 7),
  (11, 65712362363534280139543),
  (0, 38602868546842098635445292099793544258203581141646361796643693139263952299634),
  (7, 101575948255303272082238778753744148819235675596134831390567470224690205549893),
  (1, 36475206849158695213096624499536235819742999060081033689083304700770605711876),
  (3, 21602684454541409711718301348777082906531470943215473910802252801897438750443),
  (4, 63913227078364840954524293221117615740411693689411309866781777823557274530847),
  (15, 42102321027781023578874406963586677320992694676306831758048773499943989450719),
  (4, 108009715467810528162133198568558740302585386786672245969893045889884964276126),
  (2, 38879057870294481048314276966611099734210117354334130960107762530692052834582),
  (14, 67820096625905172854100632575709738322390935109183827063579514931338234268226),
  (5, 1106348587680201705542707634933038215513118911867620008350771287274083811861),
  (9, 72605138016281315146502830533485076275644867138369815760407271083474669864176),
  (7, 36647829319563667640030588038015017300928904956556984246565236165430096377969),
  (9, 12869816515236524077436231735257737835898229892109571748101060398436652427136),
  (9, 20056098123250552556344464107374966851141919234648693841798727168944066407929),
  (4, 400966789748617724693516813567715262567777551778774158302336311530117656920),
  (10, 62368630041427720680456212743323209876930262192355334039513676148559474983951),
  (2, 21010659497998128227291388684327194538336677689005634997704598368959735018665),
  (5, 45472823080726256865412891637665327968718905269169333296248494739951838516599),
  (9, 25409002065999912163513521860964671551183028525852346410812459603825104096157),
  (2, 46611781034680942234042190822941661427031377781036513541953389897673182802967),
  (8, 106822717075659207052206250287048567555689309565985291857387760380425973212601),
  (14, 15241154307182567228318423873733030265891837826769106606282605426558715607668),
  (7, 103054185518763413341437720900429198439978018046621097327160272124184028101678),
  (5, 55267490469104415652496048267925826723778010103419889150571210674404745837578),
  (8, 24800172824701057338701059743619025507917823066627727909542545714609666373572),
  (8, 34662220316463764263315420077953770201749660819475762543900181420282965941273),
  (7, 37094920302437578712914220518277619394030402664651069900717402137451662205528),
  (15, 83106149703528472027600053602241471709796083618145952724245486672096889570832),
  (12, 20728780910644260248307006130352759858880557345460612847224047047397070935348),
  (10, 53890859579005333780863544949421110279494439315624400220161956385563804828239),
  (5, 57134385014555026860104275222012768028490238702228297322560369376434601589698),
  (14, 77759024350192631898366572701714112346789559596085074318303561327322794393156),
  (14, 101707924984064567882294395208117052697398139787694557880110538218208380847471),
  (3, 69420795681248445733792075889770920208083887949070599145411741958330945344464),
  (7, 35007369813840651757570636514552568594363495500113270329468774885904759543436),
  (0, 76498948598633351125913428863663193590563330243198195283408129003482917358925),
  (6, 112030208869116535702397571011123455131309798817874070281163960715482776230551),
  (9, 55672366982465849213806727004327007536042337167411637888962840501866478325040),
  (13, 87527406467147664099094345876722435189777182410855018035256926917373676477115),
  (12, 106396903559599715611939747873523084578505972772887194661926432760125935362110),
  (11, 73684984759206862617286240912765200424100252465062071594842348980165484005167),
  (3, 115210572544323136259931743370044956215047390999507789118333411709198500766564),
  (15, 12931271046975588805068411267901169439516661877736646022404968274946814611944),
  (11, 79041110695099030325729582043195842771953506710346811651057064409142026334728),
  (4, 46872419807362498781763067658256655981181521877441635658928798242181852615563),
  (0, 38287106903381487806596844795024845528187487515989485561747806759347824233212)]

private theorem power_115792089237316195423570985008687907852837564279074904382605163141518161494337_174723607534414371449 : (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ 662715765037699607481235088557493206623080876315205958464 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907852837564279074904382605163141518161494337 7 662715765037699607481235088557493206623080876315205958464 38287106903381487806596844795024845528187487515989485561747806759347824233212 trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_174723607534414371449
    (by decide) (by decide) (by decide) (by decide)

private def trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_341948486974166000522343609283189 : List PowStep := [
  (15, 4747561509943),
  (2, 82274502583551739748738353548164736586913281731597987606633855418081771638809),
  (15, 12883510105604385561004888538397933552107465703299823760191610030313585557079),
  (3, 47514641393326128602595867547003901312871447982065725008953550847604873872809),
  (7, 44643432603165891975299920463865765648916025203332734685202979482576897433575),
  (9, 9827661712225379220007417195316747173719676190765662084631516060734730407729),
  (1, 77449024911320875210879457837481988076369059207370512157104636073434140189003),
  (14, 70840732447548301108443037686036187312100143118743263802868333587409355312346),
  (14, 37036587104333583391905673367964076289664583271256549802014195811829631262948),
  (0, 27350394653418487134154139836806564626316072236688906663808372219365256292429),
  (10, 21645045223000442108801733406317243592038949147292130200997216300512308963165),
  (12, 12484223092936350490704854662220689177176913455225993125384016944514887990539),
  (11, 72832215834264255453514948063317356839256480377313179237968977822495228207370),
  (14, 16529594909537504477406732304661758868661032308113094736066547561880041010053),
  (14, 22639174774331645304371145505464694031484396009671864666381783003229212076493),
  (7, 84196651582771782892170800858873132496568974241435511217480587763214530758678),
  (0, 90365765841991523612593180688299823178821520281751377176847502591506183294876),
  (6, 56727222613185900919300237061377425616671271340471336360571511161111720603284),
  (14, 56402776745159975403243737120741429608471921264982913850826475779713274852705),
  (9, 9703557327582425899109186838325616403669605379137712891793049286812538178430),
  (4, 28866858469423607054751515179431593992588623660244421605465176225670571055495),
  (0, 110417752627955156390819604583405341860053662367564150793441074912615069564822),
  (8, 5157557553052706430595607133914449253323019411865144347542857184414975036558),
  (12, 56473663400398063912159776325007934137684525953154527084290430482716749937061),
  (5, 25609006472828089226723221964008527365491250408466731462149172604962400180250),
  (15, 66113416961694117815567219976183346876177529731378559333609767659651960182833),
  (0, 83581669146651685322034798214115662892819594760743126915033966121920076214230),
  (12, 83423492720825299744277077303822325280916631649222345040303108480534353192612),
  (15, 60568392266446840500060129876266981446475490259295548919535121478471796113521),
  (1, 30013735472677627356608686066493419288086318587165721118211457811896229734238),
  (3, 33217930918251951045769740447287629344509115867802502875554052464326037428815),
  (4, 28879715850458899130502252619303995159225744615437994689022129556020035509753),
  (6, 29623520129646136534791970975199002965015636525055797123630278593414883737131),
  (9, 60873971765256597264966015889273493263852143139846909800043439106150606971259),
  (4, 91465238192334370693695568986532249631531425735025918828208387263542111580521),
  (4, 51891606351862416648375546863030426854805376998781551415669589105110089207805),
  (0, 40330847986065730117990277892798860778585692388550324850907595869688089295689)]

private theorem power_115792089237316195423570985008687907852837564279074904382605163141518161494337_341948486974166000522343609283189 : (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ 338624364920977752681389262317185522840540224 ≠ 1 :=
  trace_power_ne_one 115792089237316195423570985008687907852837564279074904382605163141518161494337 7 338624364920977752681389262317185522840540224 40330847986065730117990277892798860778585692388550324850907595869688089295689 trace_115792089237316195423570985008687907852837564279074904382605163141518161494337_341948486974166000522343609283189
    (by decide) (by decide) (by decide) (by decide)

theorem prime_115792089237316195423570985008687907852837564279074904382605163141518161494337 : Nat.Prime 115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
  let factors : List Nat := [2, 2, 2, 2, 2, 2, 3, 149, 631, 107361793816595537, 174723607534414371449, 341948486974166000522343609283189]
  have hf : factors.prod = 115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_149, (List.forall_mem_cons.mpr ⟨prime_631, (List.forall_mem_cons.mpr ⟨prime_107361793816595537, (List.forall_mem_cons.mpr ⟨prime_174723607534414371449, (List.forall_mem_cons.mpr ⟨prime_341948486974166000522343609283189, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 2) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_2), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 2) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_2), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 2) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_2), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 2) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_2), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 2) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_2), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 2) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_2), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 3) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_3), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 149) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_149), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 631) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_631), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 107361793816595537) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_107361793816595537), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 174723607534414371449) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_174723607534414371449), (List.forall_mem_cons.mpr ⟨(show (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) ^ ((115792089237316195423570985008687907852837564279074904382605163141518161494337 - 1) / 341948486974166000522343609283189) ≠ 1 from power_115792089237316195423570985008687907852837564279074904382605163141518161494337_341948486974166000522343609283189), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 115792089237316195423570985008687907852837564279074904382605163141518161494337 (7 : ZMod 115792089237316195423570985008687907852837564279074904382605163141518161494337) power_115792089237316195423570985008687907852837564279074904382605163141518161494337_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_491_full : List PowStep := [
  (1, 2),
  (14, 438),
  (10, 1)]

private theorem power_491_full : (2 : ZMod 491) ^ 490 = 1 :=
  trace_power 491 2 490 1 trace_491_full
    (by decide) (by decide) (by decide)

private def trace_491_2 : List PowStep := [
  (15, 362),
  (5, 490)]

private theorem power_491_2 : (2 : ZMod 491) ^ 245 ≠ 1 :=
  trace_power_ne_one 491 2 245 490 trace_491_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_491_5 : List PowStep := [
  (6, 64),
  (2, 381)]

private theorem power_491_5 : (2 : ZMod 491) ^ 98 ≠ 1 :=
  trace_power_ne_one 491 2 98 381 trace_491_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_491_7 : List PowStep := [
  (4, 16),
  (6, 138)]

private theorem power_491_7 : (2 : ZMod 491) ^ 70 ≠ 1 :=
  trace_power_ne_one 491 2 70 138 trace_491_7
    (by decide) (by decide) (by decide) (by decide)

theorem prime_491 : Nat.Prime 491 := by
  let factors : List Nat := [2, 5, 7, 7]
  have hf : factors.prod = 491 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_7, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 491) ^ ((491 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 491) ^ ((491 - 1) / 2) ≠ 1 from power_491_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 491) ^ ((491 - 1) / 5) ≠ 1 from power_491_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 491) ^ ((491 - 1) / 7) ≠ 1 from power_491_7), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 491) ^ ((491 - 1) / 7) ≠ 1 from power_491_7), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 491 (2 : ZMod 491) power_491_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_983_full : List PowStep := [
  (3, 125),
  (13, 17),
  (6, 1)]

private theorem power_983_full : (5 : ZMod 983) ^ 982 = 1 :=
  trace_power 983 5 982 1 trace_983_full
    (by decide) (by decide) (by decide)

private def trace_983_2 : List PowStep := [
  (1, 5),
  (14, 415),
  (11, 982)]

private theorem power_983_2 : (5 : ZMod 983) ^ 491 ≠ 1 :=
  trace_power_ne_one 983 5 491 982 trace_983_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_983_491 : List PowStep := [
  (2, 25)]

private theorem power_983_491 : (5 : ZMod 983) ^ 2 ≠ 1 :=
  trace_power_ne_one 983 5 2 25 trace_983_491
    (by decide) (by decide) (by decide) (by decide)

theorem prime_983 : Nat.Prime 983 := by
  let factors : List Nat := [2, 491]
  have hf : factors.prod = 983 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_491, by simp⟩)⟩)
  have hn : ∀ q ∈ factors, (5 : ZMod 983) ^ ((983 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 983) ^ ((983 - 1) / 2) ≠ 1 from power_983_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 983) ^ ((983 - 1) / 491) ≠ 1 from power_983_491), by simp⟩)⟩)
  apply lucas_primality 983 (5 : ZMod 983) power_983_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_5501_full : List PowStep := [
  (1, 2),
  (5, 1271),
  (7, 2638),
  (12, 1)]

private theorem power_5501_full : (2 : ZMod 5501) ^ 5500 = 1 :=
  trace_power 5501 2 5500 1 trace_5501_full
    (by decide) (by decide) (by decide)

private def trace_5501_2 : List PowStep := [
  (10, 1024),
  (11, 5390),
  (14, 5500)]

private theorem power_5501_2 : (2 : ZMod 5501) ^ 2750 ≠ 1 :=
  trace_power_ne_one 5501 2 2750 5500 trace_5501_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_5501_5 : List PowStep := [
  (4, 16),
  (4, 3985),
  (12, 3901)]

private theorem power_5501_5 : (2 : ZMod 5501) ^ 1100 ≠ 1 :=
  trace_power_ne_one 5501 2 1100 3901 trace_5501_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_5501_11 : List PowStep := [
  (1, 2),
  (15, 3268),
  (4, 4772)]

private theorem power_5501_11 : (2 : ZMod 5501) ^ 500 ≠ 1 :=
  trace_power_ne_one 5501 2 500 4772 trace_5501_11
    (by decide) (by decide) (by decide) (by decide)

theorem prime_5501 : Nat.Prime 5501 := by
  let factors : List Nat := [2, 2, 5, 5, 5, 11]
  have hf : factors.prod = 5501 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_11, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 5501) ^ ((5501 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5501) ^ ((5501 - 1) / 2) ≠ 1 from power_5501_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5501) ^ ((5501 - 1) / 2) ≠ 1 from power_5501_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5501) ^ ((5501 - 1) / 5) ≠ 1 from power_5501_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5501) ^ ((5501 - 1) / 5) ≠ 1 from power_5501_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5501) ^ ((5501 - 1) / 5) ≠ 1 from power_5501_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5501) ^ ((5501 - 1) / 11) ≠ 1 from power_5501_11), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 5501 (2 : ZMod 5501) power_5501_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_11003_full : List PowStep := [
  (2, 4),
  (10, 3913),
  (15, 10020),
  (10, 1)]

private theorem power_11003_full : (2 : ZMod 11003) ^ 11002 = 1 :=
  trace_power 11003 2 11002 1 trace_11003_full
    (by decide) (by decide) (by decide)

private def trace_11003_2 : List PowStep := [
  (1, 2),
  (5, 6582),
  (7, 245),
  (13, 11002)]

private theorem power_11003_2 : (2 : ZMod 11003) ^ 5501 ≠ 1 :=
  trace_power_ne_one 11003 2 5501 11002 trace_11003_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_11003_5501 : List PowStep := [
  (2, 4)]

private theorem power_11003_5501 : (2 : ZMod 11003) ^ 2 ≠ 1 :=
  trace_power_ne_one 11003 2 2 4 trace_11003_5501
    (by decide) (by decide) (by decide) (by decide)

theorem prime_11003 : Nat.Prime 11003 := by
  let factors : List Nat := [2, 5501]
  have hf : factors.prod = 11003 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5501, by simp⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 11003) ^ ((11003 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 11003) ^ ((11003 - 1) / 2) ≠ 1 from power_11003_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 11003) ^ ((11003 - 1) / 5501) ≠ 1 from power_11003_5501), by simp⟩)⟩)
  apply lucas_primality 11003 (2 : ZMod 11003) power_11003_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_449_full : List PowStep := [
  (1, 3),
  (12, 349),
  (0, 1)]

private theorem power_449_full : (3 : ZMod 449) ^ 448 = 1 :=
  trace_power 449 3 448 1 trace_449_full
    (by decide) (by decide) (by decide)

private def trace_449_2 : List PowStep := [
  (14, 221),
  (0, 448)]

private theorem power_449_2 : (3 : ZMod 449) ^ 224 ≠ 1 :=
  trace_power_ne_one 449 3 224 448 trace_449_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_449_7 : List PowStep := [
  (4, 81),
  (0, 324)]

private theorem power_449_7 : (3 : ZMod 449) ^ 64 ≠ 1 :=
  trace_power_ne_one 449 3 64 324 trace_449_7
    (by decide) (by decide) (by decide) (by decide)

theorem prime_449 : Nat.Prime 449 := by
  let factors : List Nat := [2, 2, 2, 2, 2, 2, 7]
  have hf : factors.prod = 449 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_7, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 449) ^ ((449 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 449) ^ ((449 - 1) / 2) ≠ 1 from power_449_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 449) ^ ((449 - 1) / 2) ≠ 1 from power_449_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 449) ^ ((449 - 1) / 2) ≠ 1 from power_449_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 449) ^ ((449 - 1) / 2) ≠ 1 from power_449_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 449) ^ ((449 - 1) / 2) ≠ 1 from power_449_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 449) ^ ((449 - 1) / 2) ≠ 1 from power_449_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 449) ^ ((449 - 1) / 7) ≠ 1 from power_449_7), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 449 (3 : ZMod 449) power_449_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_237073_full : List PowStep := [
  (3, 3375),
  (9, 152298),
  (14, 191961),
  (1, 107787),
  (0, 1)]

private theorem power_237073_full : (15 : ZMod 237073) ^ 237072 = 1 :=
  trace_power 237073 15 237072 1 trace_237073_full
    (by decide) (by decide) (by decide)

private def trace_237073_2 : List PowStep := [
  (1, 15),
  (12, 23410),
  (15, 159419),
  (0, 186535),
  (8, 237072)]

private theorem power_237073_2 : (15 : ZMod 237073) ^ 118536 ≠ 1 :=
  trace_power_ne_one 237073 15 118536 237072 trace_237073_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_237073_3 : List PowStep := [
  (1, 15),
  (3, 119398),
  (4, 112661),
  (11, 67392),
  (0, 63336)]

private theorem power_237073_3 : (15 : ZMod 237073) ^ 79024 ≠ 1 :=
  trace_power_ne_one 237073 15 79024 63336 trace_237073_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_237073_11 : List PowStep := [
  (5, 48156),
  (4, 139266),
  (3, 206878),
  (0, 224235)]

private theorem power_237073_11 : (15 : ZMod 237073) ^ 21552 ≠ 1 :=
  trace_power_ne_one 237073 15 21552 224235 trace_237073_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_237073_449 : List PowStep := [
  (2, 225),
  (1, 49845),
  (0, 197030)]

private theorem power_237073_449 : (15 : ZMod 237073) ^ 528 ≠ 1 :=
  trace_power_ne_one 237073 15 528 197030 trace_237073_449
    (by decide) (by decide) (by decide) (by decide)

theorem prime_237073 : Nat.Prime 237073 := by
  let factors : List Nat := [2, 2, 2, 2, 3, 11, 449]
  have hf : factors.prod = 237073 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_449, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (15 : ZMod 237073) ^ ((237073 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (15 : ZMod 237073) ^ ((237073 - 1) / 2) ≠ 1 from power_237073_2), (List.forall_mem_cons.mpr ⟨(show (15 : ZMod 237073) ^ ((237073 - 1) / 2) ≠ 1 from power_237073_2), (List.forall_mem_cons.mpr ⟨(show (15 : ZMod 237073) ^ ((237073 - 1) / 2) ≠ 1 from power_237073_2), (List.forall_mem_cons.mpr ⟨(show (15 : ZMod 237073) ^ ((237073 - 1) / 2) ≠ 1 from power_237073_2), (List.forall_mem_cons.mpr ⟨(show (15 : ZMod 237073) ^ ((237073 - 1) / 3) ≠ 1 from power_237073_3), (List.forall_mem_cons.mpr ⟨(show (15 : ZMod 237073) ^ ((237073 - 1) / 11) ≠ 1 from power_237073_11), (List.forall_mem_cons.mpr ⟨(show (15 : ZMod 237073) ^ ((237073 - 1) / 449) ≠ 1 from power_237073_449), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 237073 (15 : ZMod 237073) power_237073_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_3691_full : List PowStep := [
  (14, 1620),
  (6, 2147),
  (10, 1)]

private theorem power_3691_full : (2 : ZMod 3691) ^ 3690 = 1 :=
  trace_power 3691 2 3690 1 trace_3691_full
    (by decide) (by decide) (by decide)

private def trace_3691_2 : List PowStep := [
  (7, 128),
  (3, 3226),
  (5, 3690)]

private theorem power_3691_2 : (2 : ZMod 3691) ^ 1845 ≠ 1 :=
  trace_power_ne_one 3691 2 1845 3690 trace_3691_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_3691_3 : List PowStep := [
  (4, 16),
  (12, 2161),
  (14, 3216)]

private theorem power_3691_3 : (2 : ZMod 3691) ^ 1230 ≠ 1 :=
  trace_power_ne_one 3691 2 1230 3216 trace_3691_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_3691_5 : List PowStep := [
  (2, 4),
  (14, 835),
  (2, 643)]

private theorem power_3691_5 : (2 : ZMod 3691) ^ 738 ≠ 1 :=
  trace_power_ne_one 3691 2 738 643 trace_3691_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_3691_41 : List PowStep := [
  (5, 32),
  (10, 1752)]

private theorem power_3691_41 : (2 : ZMod 3691) ^ 90 ≠ 1 :=
  trace_power_ne_one 3691 2 90 1752 trace_3691_41
    (by decide) (by decide) (by decide) (by decide)

theorem prime_3691 : Nat.Prime 3691 := by
  let factors : List Nat := [2, 3, 3, 5, 41]
  have hf : factors.prod = 3691 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_41, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 3691) ^ ((3691 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 3691) ^ ((3691 - 1) / 2) ≠ 1 from power_3691_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 3691) ^ ((3691 - 1) / 3) ≠ 1 from power_3691_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 3691) ^ ((3691 - 1) / 3) ≠ 1 from power_3691_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 3691) ^ ((3691 - 1) / 5) ≠ 1 from power_3691_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 3691) ^ ((3691 - 1) / 41) ≠ 1 from power_3691_41), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 3691 (2 : ZMod 3691) power_3691_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_4999_full : List PowStep := [
  (1, 3),
  (3, 3965),
  (8, 2406),
  (6, 1)]

private theorem power_4999_full : (3 : ZMod 4999) ^ 4998 = 1 :=
  trace_power 4999 3 4998 1 trace_4999_full
    (by decide) (by decide) (by decide)

private def trace_4999_2 : List PowStep := [
  (9, 4686),
  (12, 180),
  (3, 4998)]

private theorem power_4999_2 : (3 : ZMod 4999) ^ 2499 ≠ 1 :=
  trace_power_ne_one 4999 3 2499 4998 trace_4999_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_4999_3 : List PowStep := [
  (6, 729),
  (8, 641),
  (2, 2661)]

private theorem power_4999_3 : (3 : ZMod 4999) ^ 1666 ≠ 1 :=
  trace_power_ne_one 4999 3 1666 2661 trace_4999_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_4999_7 : List PowStep := [
  (2, 9),
  (12, 638),
  (10, 227)]

private theorem power_4999_7 : (3 : ZMod 4999) ^ 714 ≠ 1 :=
  trace_power_ne_one 4999 3 714 227 trace_4999_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_4999_17 : List PowStep := [
  (1, 3),
  (2, 2988),
  (6, 2420)]

private theorem power_4999_17 : (3 : ZMod 4999) ^ 294 ≠ 1 :=
  trace_power_ne_one 4999 3 294 2420 trace_4999_17
    (by decide) (by decide) (by decide) (by decide)

theorem prime_4999 : Nat.Prime 4999 := by
  let factors : List Nat := [2, 3, 7, 7, 17]
  have hf : factors.prod = 4999 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_17, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 4999) ^ ((4999 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 4999) ^ ((4999 - 1) / 2) ≠ 1 from power_4999_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 4999) ^ ((4999 - 1) / 3) ≠ 1 from power_4999_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 4999) ^ ((4999 - 1) / 7) ≠ 1 from power_4999_7), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 4999) ^ ((4999 - 1) / 7) ≠ 1 from power_4999_7), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 4999) ^ ((4999 - 1) / 17) ≠ 1 from power_4999_17), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 4999 (3 : ZMod 4999) power_4999_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_405928799_full : List PowStep := [
  (1, 22),
  (8, 51831449),
  (3, 84246942),
  (1, 195132274),
  (15, 367571520),
  (11, 358932488),
  (5, 347753120),
  (14, 1)]

private theorem power_405928799_full : (22 : ZMod 405928799) ^ 405928798 = 1 :=
  trace_power 405928799 22 405928798 1 trace_405928799_full
    (by decide) (by decide) (by decide)

private def trace_405928799_2 : List PowStep := [
  (12, 306932537),
  (1, 5523534),
  (8, 118807673),
  (15, 306437870),
  (13, 166293004),
  (10, 307435558),
  (15, 405928798)]

private theorem power_405928799_2 : (22 : ZMod 405928799) ^ 202964399 ≠ 1 :=
  trace_power_ne_one 405928799 22 202964399 405928798 trace_405928799_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_405928799_11 : List PowStep := [
  (2, 484),
  (3, 135557996),
  (3, 67966445),
  (1, 244532896),
  (6, 253721944),
  (13, 268247625),
  (10, 215859951)]

private theorem power_405928799_11 : (22 : ZMod 405928799) ^ 36902618 ≠ 1 :=
  trace_power_ne_one 405928799 22 36902618 215859951 trace_405928799_11
    (by decide) (by decide) (by decide) (by decide)

private def trace_405928799_3691 : List PowStep := [
  (1, 22),
  (10, 324764577),
  (13, 268588283),
  (9, 350022274),
  (10, 147917081)]

private theorem power_405928799_3691 : (22 : ZMod 405928799) ^ 109978 ≠ 1 :=
  trace_power_ne_one 405928799 22 109978 147917081 trace_405928799_3691
    (by decide) (by decide) (by decide) (by decide)

private def trace_405928799_4999 : List PowStep := [
  (1, 22),
  (3, 295921102),
  (13, 403887925),
  (3, 18407859),
  (2, 61847818)]

private theorem power_405928799_4999 : (22 : ZMod 405928799) ^ 81202 ≠ 1 :=
  trace_power_ne_one 405928799 22 81202 61847818 trace_405928799_4999
    (by decide) (by decide) (by decide) (by decide)

theorem prime_405928799 : Nat.Prime 405928799 := by
  let factors : List Nat := [2, 11, 3691, 4999]
  have hf : factors.prod = 405928799 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_11, (List.forall_mem_cons.mpr ⟨prime_3691, (List.forall_mem_cons.mpr ⟨prime_4999, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (22 : ZMod 405928799) ^ ((405928799 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (22 : ZMod 405928799) ^ ((405928799 - 1) / 2) ≠ 1 from power_405928799_2), (List.forall_mem_cons.mpr ⟨(show (22 : ZMod 405928799) ^ ((405928799 - 1) / 11) ≠ 1 from power_405928799_11), (List.forall_mem_cons.mpr ⟨(show (22 : ZMod 405928799) ^ ((405928799 - 1) / 3691) ≠ 1 from power_405928799_3691), (List.forall_mem_cons.mpr ⟨(show (22 : ZMod 405928799) ^ ((405928799 - 1) / 4999) ≠ 1 from power_405928799_4999), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 405928799 (22 : ZMod 405928799) power_405928799_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_107_full : List PowStep := [
  (6, 64),
  (10, 1)]

private theorem power_107_full : (2 : ZMod 107) ^ 106 = 1 :=
  trace_power 107 2 106 1 trace_107_full
    (by decide) (by decide) (by decide)

private def trace_107_2 : List PowStep := [
  (3, 8),
  (5, 106)]

private theorem power_107_2 : (2 : ZMod 107) ^ 53 ≠ 1 :=
  trace_power_ne_one 107 2 53 106 trace_107_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_107_53 : List PowStep := [
  (2, 4)]

private theorem power_107_53 : (2 : ZMod 107) ^ 2 ≠ 1 :=
  trace_power_ne_one 107 2 2 4 trace_107_53
    (by decide) (by decide) (by decide) (by decide)

theorem prime_107 : Nat.Prime 107 := by
  let factors : List Nat := [2, 53]
  have hf : factors.prod = 107 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_53, by simp⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 107) ^ ((107 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 107) ^ ((107 - 1) / 2) ≠ 1 from power_107_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 107) ^ ((107 - 1) / 53) ≠ 1 from power_107_53), by simp⟩)⟩)
  apply lucas_primality 107 (2 : ZMod 107) power_107_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_661_full : List PowStep := [
  (2, 4),
  (9, 40),
  (4, 1)]

private theorem power_661_full : (2 : ZMod 661) ^ 660 = 1 :=
  trace_power 661 2 660 1 trace_661_full
    (by decide) (by decide) (by decide)

private def trace_661_2 : List PowStep := [
  (1, 2),
  (4, 230),
  (10, 660)]

private theorem power_661_2 : (2 : ZMod 661) ^ 330 ≠ 1 :=
  trace_power_ne_one 661 2 330 660 trace_661_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_661_3 : List PowStep := [
  (13, 260),
  (12, 296)]

private theorem power_661_3 : (2 : ZMod 661) ^ 220 ≠ 1 :=
  trace_power_ne_one 661 2 220 296 trace_661_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_661_5 : List PowStep := [
  (8, 256),
  (4, 247)]

private theorem power_661_5 : (2 : ZMod 661) ^ 132 ≠ 1 :=
  trace_power_ne_one 661 2 132 247 trace_661_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_661_11 : List PowStep := [
  (3, 8),
  (12, 634)]

private theorem power_661_11 : (2 : ZMod 661) ^ 60 ≠ 1 :=
  trace_power_ne_one 661 2 60 634 trace_661_11
    (by decide) (by decide) (by decide) (by decide)

theorem prime_661 : Nat.Prime 661 := by
  let factors : List Nat := [2, 2, 3, 5, 11]
  have hf : factors.prod = 661 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_11, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 661) ^ ((661 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 661) ^ ((661 - 1) / 2) ≠ 1 from power_661_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 661) ^ ((661 - 1) / 2) ≠ 1 from power_661_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 661) ^ ((661 - 1) / 3) ≠ 1 from power_661_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 661) ^ ((661 - 1) / 5) ≠ 1 from power_661_5), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 661) ^ ((661 - 1) / 11) ≠ 1 from power_661_11), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 661 (2 : ZMod 661) power_661_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_93001_full : List PowStep := [
  (1, 14),
  (6, 91157),
  (11, 33876),
  (4, 46468),
  (8, 1)]

private theorem power_93001_full : (14 : ZMod 93001) ^ 93000 = 1 :=
  trace_power 93001 14 93000 1 trace_93001_full
    (by decide) (by decide) (by decide)

private def trace_93001_2 : List PowStep := [
  (11, 27421),
  (5, 26718),
  (10, 29081),
  (4, 93000)]

private theorem power_93001_2 : (14 : ZMod 93001) ^ 46500 ≠ 1 :=
  trace_power_ne_one 93001 14 46500 93000 trace_93001_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_93001_3 : List PowStep := [
  (7, 43371),
  (9, 85175),
  (1, 80939),
  (8, 22786)]

private theorem power_93001_3 : (14 : ZMod 93001) ^ 31000 ≠ 1 :=
  trace_power_ne_one 93001 14 31000 22786 trace_93001_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_93001_5 : List PowStep := [
  (4, 38416),
  (8, 8867),
  (10, 48417),
  (8, 79997)]

private theorem power_93001_5 : (14 : ZMod 93001) ^ 18600 ≠ 1 :=
  trace_power_ne_one 93001 14 18600 79997 trace_93001_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_93001_31 : List PowStep := [
  (11, 27421),
  (11, 52709),
  (8, 61219)]

private theorem power_93001_31 : (14 : ZMod 93001) ^ 3000 ≠ 1 :=
  trace_power_ne_one 93001 14 3000 61219 trace_93001_31
    (by decide) (by decide) (by decide) (by decide)

theorem prime_93001 : Nat.Prime 93001 := by
  let factors : List Nat := [2, 2, 2, 3, 5, 5, 5, 31]
  have hf : factors.prod = 93001 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_31, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (14 : ZMod 93001) ^ ((93001 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 93001) ^ ((93001 - 1) / 2) ≠ 1 from power_93001_2), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 93001) ^ ((93001 - 1) / 2) ≠ 1 from power_93001_2), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 93001) ^ ((93001 - 1) / 2) ≠ 1 from power_93001_2), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 93001) ^ ((93001 - 1) / 3) ≠ 1 from power_93001_3), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 93001) ^ ((93001 - 1) / 5) ≠ 1 from power_93001_5), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 93001) ^ ((93001 - 1) / 5) ≠ 1 from power_93001_5), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 93001) ^ ((93001 - 1) / 5) ≠ 1 from power_93001_5), (List.forall_mem_cons.mpr ⟨(show (14 : ZMod 93001) ^ ((93001 - 1) / 31) ≠ 1 from power_93001_31), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 93001 (14 : ZMod 93001) power_93001_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_12048837557_full : List PowStep := [
  (2, 4),
  (12, 883211196),
  (14, 7981552270),
  (2, 8474336178),
  (10, 9426048753),
  (10, 284884293),
  (11, 4016385526),
  (11, 11446980907),
  (4, 1)]

private theorem power_12048837557_full : (2 : ZMod 12048837557) ^ 12048837556 = 1 :=
  trace_power 12048837557 2 12048837556 1 trace_12048837557_full
    (by decide) (by decide) (by decide)

private def trace_12048837557_2 : List PowStep := [
  (1, 2),
  (6, 4194304),
  (7, 11894905327),
  (1, 4490516767),
  (5, 2401545910),
  (5, 9644260193),
  (5, 5458521508),
  (13, 560724773),
  (10, 12048837556)]

private theorem power_12048837557_2 : (2 : ZMod 12048837557) ^ 6024418778 ≠ 1 :=
  trace_power_ne_one 12048837557 2 6024418778 12048837556 trace_12048837557_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_12048837557_7 : List PowStep := [
  (6, 64),
  (6, 1095104075),
  (9, 4418382881),
  (8, 7938344963),
  (6, 11105654168),
  (1, 8108342189),
  (10, 11739727391),
  (12, 41029474)]

private theorem power_12048837557_7 : (2 : ZMod 12048837557) ^ 1721262508 ≠ 1 :=
  trace_power_ne_one 12048837557 2 1721262508 41029474 trace_12048837557_7
    (by decide) (by decide) (by decide) (by decide)

private def trace_12048837557_661 : List PowStep := [
  (1, 2),
  (1, 131072),
  (6, 8342573050),
  (2, 5445132129),
  (3, 9243528609),
  (14, 10312932194),
  (4, 8877273464)]

private theorem power_12048837557_661 : (2 : ZMod 12048837557) ^ 18228196 ≠ 1 :=
  trace_power_ne_one 12048837557 2 18228196 8877273464 trace_12048837557_661
    (by decide) (by decide) (by decide) (by decide)

private def trace_12048837557_93001 : List PowStep := [
  (1, 2),
  (15, 2147483648),
  (10, 7480721140),
  (1, 2062192906),
  (4, 4746995210)]

private theorem power_12048837557_93001 : (2 : ZMod 12048837557) ^ 129556 ≠ 1 :=
  trace_power_ne_one 12048837557 2 129556 4746995210 trace_12048837557_93001
    (by decide) (by decide) (by decide) (by decide)

theorem prime_12048837557 : Nat.Prime 12048837557 := by
  let factors : List Nat := [2, 2, 7, 7, 661, 93001]
  have hf : factors.prod = 12048837557 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_7, (List.forall_mem_cons.mpr ⟨prime_661, (List.forall_mem_cons.mpr ⟨prime_93001, by simp⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 12048837557) ^ ((12048837557 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 12048837557) ^ ((12048837557 - 1) / 2) ≠ 1 from power_12048837557_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 12048837557) ^ ((12048837557 - 1) / 2) ≠ 1 from power_12048837557_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 12048837557) ^ ((12048837557 - 1) / 7) ≠ 1 from power_12048837557_7), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 12048837557) ^ ((12048837557 - 1) / 7) ≠ 1 from power_12048837557_7), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 12048837557) ^ ((12048837557 - 1) / 661) ≠ 1 from power_12048837557_661), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 12048837557) ^ ((12048837557 - 1) / 93001) ≠ 1 from power_12048837557_93001), by simp⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 12048837557 (2 : ZMod 12048837557) power_12048837557_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_5156902474397_full : List PowStep := [
  (4, 16),
  (11, 3612365223546),
  (0, 1476751069562),
  (10, 3044316283765),
  (15, 1163788361085),
  (5, 2550693829131),
  (7, 24272984856),
  (1, 3400251867718),
  (2, 599630194631),
  (9, 1040775521777),
  (12, 1)]

private theorem power_5156902474397_full : (2 : ZMod 5156902474397) ^ 5156902474396 = 1 :=
  trace_power 5156902474397 2 5156902474396 1 trace_5156902474397_full
    (by decide) (by decide) (by decide)

private def trace_5156902474397_2 : List PowStep := [
  (2, 4),
  (5, 137438953472),
  (8, 2243617552499),
  (5, 3891323020129),
  (7, 1806583742645),
  (10, 39450837500),
  (11, 1155868772095),
  (8, 242280007350),
  (9, 179134234739),
  (4, 4377102515264),
  (14, 5156902474396)]

private theorem power_5156902474397_2 : (2 : ZMod 5156902474397) ^ 2578451237198 ≠ 1 :=
  trace_power_ne_one 5156902474397 2 2578451237198 5156902474396 trace_5156902474397_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_5156902474397_107 : List PowStep := [
  (11, 2048),
  (3, 3957423448215),
  (8, 2203038787765),
  (10, 2757631940018),
  (10, 3981764034225),
  (10, 417457207361),
  (14, 1184050977974),
  (13, 3481135916060),
  (4, 4827909776387)]

private theorem power_5156902474397_107 : (2 : ZMod 5156902474397) ^ 48195350228 ≠ 1 :=
  trace_power_ne_one 5156902474397 2 48195350228 4827909776387 trace_5156902474397_107
    (by decide) (by decide) (by decide) (by decide)

private def trace_5156902474397_12048837557 : List PowStep := [
  (1, 2),
  (10, 67108864),
  (12, 4746712836098)]

private theorem power_5156902474397_12048837557 : (2 : ZMod 5156902474397) ^ 428 ≠ 1 :=
  trace_power_ne_one 5156902474397 2 428 4746712836098 trace_5156902474397_12048837557
    (by decide) (by decide) (by decide) (by decide)

theorem prime_5156902474397 : Nat.Prime 5156902474397 := by
  let factors : List Nat := [2, 2, 107, 12048837557]
  have hf : factors.prod = 5156902474397 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_107, (List.forall_mem_cons.mpr ⟨prime_12048837557, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 5156902474397) ^ ((5156902474397 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5156902474397) ^ ((5156902474397 - 1) / 2) ≠ 1 from power_5156902474397_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5156902474397) ^ ((5156902474397 - 1) / 2) ≠ 1 from power_5156902474397_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5156902474397) ^ ((5156902474397 - 1) / 107) ≠ 1 from power_5156902474397_107), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 5156902474397) ^ ((5156902474397 - 1) / 12048837557) ≠ 1 from power_5156902474397_12048837557), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 5156902474397 (2 : ZMod 5156902474397) power_5156902474397_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_1670836401704629_full : List PowStep := [
  (5, 32),
  (14, 334550377564754),
  (15, 697087771204285),
  (9, 1096796053977318),
  (13, 393450958863751),
  (14, 1408413978844002),
  (10, 351800355889703),
  (3, 932282227416658),
  (3, 1417046708254361),
  (8, 1073117598149064),
  (14, 1314053965769530),
  (11, 879277017913070),
  (4, 1)]

private theorem power_1670836401704629_full : (2 : ZMod 1670836401704629) ^ 1670836401704628 = 1 :=
  trace_power 1670836401704629 2 1670836401704628 1 trace_1670836401704629_full
    (by decide) (by decide) (by decide)

private def trace_1670836401704629_2 : List PowStep := [
  (2, 4),
  (15, 140737488355328),
  (7, 78886445969736),
  (12, 942329548201887),
  (14, 531531781777348),
  (15, 477728264953292),
  (5, 430826919595042),
  (1, 126810643008675),
  (9, 973435405542231),
  (12, 1018664538146646),
  (7, 1342255429129415),
  (5, 378776392996913),
  (10, 1670836401704628)]

private theorem power_1670836401704629_2 : (2 : ZMod 1670836401704629) ^ 835418200852314 ≠ 1 :=
  trace_power_ne_one 1670836401704629 2 835418200852314 1670836401704628 trace_1670836401704629_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_1670836401704629_3 : List PowStep := [
  (1, 2),
  (15, 2147483648),
  (10, 1630060553903927),
  (8, 424461706918998),
  (9, 1038893697534927),
  (15, 244842569073087),
  (8, 689720735855157),
  (11, 73126903649427),
  (11, 777470217300954),
  (13, 567221491216497),
  (10, 1649866683717563),
  (3, 512062820541085),
  (12, 1322408984917240)]

private theorem power_1670836401704629_3 : (2 : ZMod 1670836401704629) ^ 556945467234876 ≠ 1 :=
  trace_power_ne_one 1670836401704629 2 556945467234876 1322408984917240 trace_1670836401704629_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_1670836401704629_5156902474397 : List PowStep := [
  (1, 2),
  (4, 1048576),
  (4, 11046204280772)]

private theorem power_1670836401704629_5156902474397 : (2 : ZMod 1670836401704629) ^ 324 ≠ 1 :=
  trace_power_ne_one 1670836401704629 2 324 11046204280772 trace_1670836401704629_5156902474397
    (by decide) (by decide) (by decide) (by decide)

theorem prime_1670836401704629 : Nat.Prime 1670836401704629 := by
  let factors : List Nat := [2, 2, 3, 3, 3, 3, 5156902474397]
  have hf : factors.prod = 1670836401704629 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_5156902474397, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 1670836401704629) ^ ((1670836401704629 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1670836401704629) ^ ((1670836401704629 - 1) / 2) ≠ 1 from power_1670836401704629_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1670836401704629) ^ ((1670836401704629 - 1) / 2) ≠ 1 from power_1670836401704629_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1670836401704629) ^ ((1670836401704629 - 1) / 3) ≠ 1 from power_1670836401704629_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1670836401704629) ^ ((1670836401704629 - 1) / 3) ≠ 1 from power_1670836401704629_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1670836401704629) ^ ((1670836401704629 - 1) / 3) ≠ 1 from power_1670836401704629_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1670836401704629) ^ ((1670836401704629 - 1) / 3) ≠ 1 from power_1670836401704629_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1670836401704629) ^ ((1670836401704629 - 1) / 5156902474397) ≠ 1 from power_1670836401704629_5156902474397), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 1670836401704629 (2 : ZMod 1670836401704629) power_1670836401704629_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_137_full : List PowStep := [
  (8, 122),
  (8, 1)]

private theorem power_137_full : (3 : ZMod 137) ^ 136 = 1 :=
  trace_power 137 3 136 1 trace_137_full
    (by decide) (by decide) (by decide)

private def trace_137_2 : List PowStep := [
  (4, 81),
  (4, 136)]

private theorem power_137_2 : (3 : ZMod 137) ^ 68 ≠ 1 :=
  trace_power_ne_one 137 3 68 136 trace_137_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_137_17 : List PowStep := [
  (8, 122)]

private theorem power_137_17 : (3 : ZMod 137) ^ 8 ≠ 1 :=
  trace_power_ne_one 137 3 8 122 trace_137_17
    (by decide) (by decide) (by decide) (by decide)

theorem prime_137 : Nat.Prime 137 := by
  let factors : List Nat := [2, 2, 2, 17]
  have hf : factors.prod = 137 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_17, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 137) ^ ((137 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 137) ^ ((137 - 1) / 2) ≠ 1 from power_137_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 137) ^ ((137 - 1) / 2) ≠ 1 from power_137_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 137) ^ ((137 - 1) / 2) ≠ 1 from power_137_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 137) ^ ((137 - 1) / 17) ≠ 1 from power_137_17), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 137 (3 : ZMod 137) power_137_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_823_full : List PowStep := [
  (3, 27),
  (3, 371),
  (6, 1)]

private theorem power_823_full : (3 : ZMod 823) ^ 822 = 1 :=
  trace_power 823 3 822 1 trace_823_full
    (by decide) (by decide) (by decide)

private def trace_823_2 : List PowStep := [
  (1, 3),
  (9, 534),
  (11, 822)]

private theorem power_823_2 : (3 : ZMod 823) ^ 411 ≠ 1 :=
  trace_power_ne_one 823 3 411 822 trace_823_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_823_3 : List PowStep := [
  (1, 3),
  (1, 764),
  (2, 648)]

private theorem power_823_3 : (3 : ZMod 823) ^ 274 ≠ 1 :=
  trace_power_ne_one 823 3 274 648 trace_823_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_823_137 : List PowStep := [
  (6, 729)]

private theorem power_823_137 : (3 : ZMod 823) ^ 6 ≠ 1 :=
  trace_power_ne_one 823 3 6 729 trace_823_137
    (by decide) (by decide) (by decide) (by decide)

theorem prime_823 : Nat.Prime 823 := by
  let factors : List Nat := [2, 3, 137]
  have hf : factors.prod = 823 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_137, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 823) ^ ((823 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 823) ^ ((823 - 1) / 2) ≠ 1 from power_823_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 823) ^ ((823 - 1) / 3) ≠ 1 from power_823_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 823) ^ ((823 - 1) / 137) ≠ 1 from power_823_137), by simp⟩)⟩)⟩)
  apply lucas_primality 823 (3 : ZMod 823) power_823_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_47 : Nat.Prime 47 := by decide

private def trace_223_full : List PowStep := [
  (13, 96),
  (14, 1)]

private theorem power_223_full : (3 : ZMod 223) ^ 222 = 1 :=
  trace_power 223 3 222 1 trace_223_full
    (by decide) (by decide) (by decide)

private def trace_223_2 : List PowStep := [
  (6, 60),
  (15, 222)]

private theorem power_223_2 : (3 : ZMod 223) ^ 111 ≠ 1 :=
  trace_power_ne_one 223 3 111 222 trace_223_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_223_3 : List PowStep := [
  (4, 81),
  (10, 183)]

private theorem power_223_3 : (3 : ZMod 223) ^ 74 ≠ 1 :=
  trace_power_ne_one 223 3 74 183 trace_223_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_223_37 : List PowStep := [
  (6, 60)]

private theorem power_223_37 : (3 : ZMod 223) ^ 6 ≠ 1 :=
  trace_power_ne_one 223 3 6 60 trace_223_37
    (by decide) (by decide) (by decide) (by decide)

theorem prime_223 : Nat.Prime 223 := by
  let factors : List Nat := [2, 3, 37]
  have hf : factors.prod = 223 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_37, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 223) ^ ((223 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 223) ^ ((223 - 1) / 2) ≠ 1 from power_223_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 223) ^ ((223 - 1) / 3) ≠ 1 from power_223_3), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 223) ^ ((223 - 1) / 37) ≠ 1 from power_223_37), by simp⟩)⟩)⟩)
  apply lucas_primality 223 (3 : ZMod 223) power_223_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_20963_full : List PowStep := [
  (5, 32),
  (1, 10483),
  (14, 12902),
  (2, 1)]

private theorem power_20963_full : (2 : ZMod 20963) ^ 20962 = 1 :=
  trace_power 20963 2 20962 1 trace_20963_full
    (by decide) (by decide) (by decide)

private def trace_20963_2 : List PowStep := [
  (2, 4),
  (8, 13772),
  (15, 13762),
  (1, 20962)]

private theorem power_20963_2 : (2 : ZMod 20963) ^ 10481 ≠ 1 :=
  trace_power_ne_one 20963 2 10481 20962 trace_20963_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_20963_47 : List PowStep := [
  (1, 2),
  (11, 12602),
  (14, 4773)]

private theorem power_20963_47 : (2 : ZMod 20963) ^ 446 ≠ 1 :=
  trace_power_ne_one 20963 2 446 4773 trace_20963_47
    (by decide) (by decide) (by decide) (by decide)

private def trace_20963_223 : List PowStep := [
  (5, 32),
  (14, 12288)]

private theorem power_20963_223 : (2 : ZMod 20963) ^ 94 ≠ 1 :=
  trace_power_ne_one 20963 2 94 12288 trace_20963_223
    (by decide) (by decide) (by decide) (by decide)

theorem prime_20963 : Nat.Prime 20963 := by
  let factors : List Nat := [2, 47, 223]
  have hf : factors.prod = 20963 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_47, (List.forall_mem_cons.mpr ⟨prime_223, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 20963) ^ ((20963 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 20963) ^ ((20963 - 1) / 2) ≠ 1 from power_20963_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 20963) ^ ((20963 - 1) / 47) ≠ 1 from power_20963_47), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 20963) ^ ((20963 - 1) / 223) ≠ 1 from power_20963_223), by simp⟩)⟩)⟩)
  apply lucas_primality 20963 (2 : ZMod 20963) power_20963_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_41927_full : List PowStep := [
  (10, 38561),
  (3, 39602),
  (12, 21564),
  (6, 1)]

private theorem power_41927_full : (5 : ZMod 41927) ^ 41926 = 1 :=
  trace_power 41927 5 41926 1 trace_41927_full
    (by decide) (by decide) (by decide)

private def trace_41927_2 : List PowStep := [
  (5, 3125),
  (1, 41573),
  (14, 13546),
  (3, 41926)]

private theorem power_41927_2 : (5 : ZMod 41927) ^ 20963 ≠ 1 :=
  trace_power_ne_one 41927 5 20963 41926 trace_41927_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_41927_20963 : List PowStep := [
  (2, 25)]

private theorem power_41927_20963 : (5 : ZMod 41927) ^ 2 ≠ 1 :=
  trace_power_ne_one 41927 5 2 25 trace_41927_20963
    (by decide) (by decide) (by decide) (by decide)

theorem prime_41927 : Nat.Prime 41927 := by
  let factors : List Nat := [2, 20963]
  have hf : factors.prod = 41927 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_20963, by simp⟩)⟩)
  have hn : ∀ q ∈ factors, (5 : ZMod 41927) ^ ((41927 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 41927) ^ ((41927 - 1) / 2) ≠ 1 from power_41927_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 41927) ^ ((41927 - 1) / 20963) ≠ 1 from power_41927_20963), by simp⟩)⟩)
  apply lucas_primality 41927 (5 : ZMod 41927) power_41927_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_1593227_full : List PowStep := [
  (1, 2),
  (8, 844946),
  (4, 523907),
  (15, 241474),
  (8, 341497),
  (10, 1)]

private theorem power_1593227_full : (2 : ZMod 1593227) ^ 1593226 = 1 :=
  trace_power 1593227 2 1593226 1 trace_1593227_full
    (by decide) (by decide) (by decide)

private def trace_1593227_2 : List PowStep := [
  (12, 4096),
  (2, 474025),
  (7, 209485),
  (12, 1278346),
  (5, 1593226)]

private theorem power_1593227_2 : (2 : ZMod 1593227) ^ 796613 ≠ 1 :=
  trace_power_ne_one 1593227 2 796613 1593226 trace_1593227_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_1593227_19 : List PowStep := [
  (1, 2),
  (4, 1048576),
  (7, 1558345),
  (8, 268547),
  (14, 836782)]

private theorem power_1593227_19 : (2 : ZMod 1593227) ^ 83854 ≠ 1 :=
  trace_power_ne_one 1593227 2 83854 836782 trace_1593227_19
    (by decide) (by decide) (by decide) (by decide)

private def trace_1593227_41927 : List PowStep := [
  (2, 4),
  (6, 45861)]

private theorem power_1593227_41927 : (2 : ZMod 1593227) ^ 38 ≠ 1 :=
  trace_power_ne_one 1593227 2 38 45861 trace_1593227_41927
    (by decide) (by decide) (by decide) (by decide)

theorem prime_1593227 : Nat.Prime 1593227 := by
  let factors : List Nat := [2, 19, 41927]
  have hf : factors.prod = 1593227 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_19, (List.forall_mem_cons.mpr ⟨prime_41927, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 1593227) ^ ((1593227 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1593227) ^ ((1593227 - 1) / 2) ≠ 1 from power_1593227_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1593227) ^ ((1593227 - 1) / 19) ≠ 1 from power_1593227_19), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1593227) ^ ((1593227 - 1) / 41927) ≠ 1 from power_1593227_41927), by simp⟩)⟩)⟩)
  apply lucas_primality 1593227 (2 : ZMod 1593227) power_1593227_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_379_full : List PowStep := [
  (1, 2),
  (7, 201),
  (10, 1)]

private theorem power_379_full : (2 : ZMod 379) ^ 378 = 1 :=
  trace_power 379 2 378 1 trace_379_full
    (by decide) (by decide) (by decide)

private def trace_379_2 : List PowStep := [
  (11, 153),
  (13, 378)]

private theorem power_379_2 : (2 : ZMod 379) ^ 189 ≠ 1 :=
  trace_power_ne_one 379 2 189 378 trace_379_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_379_3 : List PowStep := [
  (7, 128),
  (14, 327)]

private theorem power_379_3 : (2 : ZMod 379) ^ 126 ≠ 1 :=
  trace_power_ne_one 379 2 126 327 trace_379_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_379_7 : List PowStep := [
  (3, 8),
  (6, 125)]

private theorem power_379_7 : (2 : ZMod 379) ^ 54 ≠ 1 :=
  trace_power_ne_one 379 2 54 125 trace_379_7
    (by decide) (by decide) (by decide) (by decide)

theorem prime_379 : Nat.Prime 379 := by
  let factors : List Nat := [2, 3, 3, 3, 7]
  have hf : factors.prod = 379 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_7, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 379) ^ ((379 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 379) ^ ((379 - 1) / 2) ≠ 1 from power_379_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 379) ^ ((379 - 1) / 3) ≠ 1 from power_379_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 379) ^ ((379 - 1) / 3) ≠ 1 from power_379_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 379) ^ ((379 - 1) / 3) ≠ 1 from power_379_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 379) ^ ((379 - 1) / 7) ≠ 1 from power_379_7), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 379 (2 : ZMod 379) power_379_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_409_full : List PowStep := [
  (1, 21),
  (9, 105),
  (8, 1)]

private theorem power_409_full : (21 : ZMod 409) ^ 408 = 1 :=
  trace_power 409 21 408 1 trace_409_full
    (by decide) (by decide) (by decide)

private def trace_409_2 : List PowStep := [
  (12, 259),
  (12, 408)]

private theorem power_409_2 : (21 : ZMod 409) ^ 204 ≠ 1 :=
  trace_power_ne_one 409 21 204 408 trace_409_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_409_3 : List PowStep := [
  (8, 309),
  (8, 355)]

private theorem power_409_3 : (21 : ZMod 409) ^ 136 ≠ 1 :=
  trace_power_ne_one 409 21 136 355 trace_409_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_409_17 : List PowStep := [
  (1, 21),
  (8, 5)]

private theorem power_409_17 : (21 : ZMod 409) ^ 24 ≠ 1 :=
  trace_power_ne_one 409 21 24 5 trace_409_17
    (by decide) (by decide) (by decide) (by decide)

theorem prime_409 : Nat.Prime 409 := by
  let factors : List Nat := [2, 2, 2, 3, 17]
  have hf : factors.prod = 409 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_17, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (21 : ZMod 409) ^ ((409 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (21 : ZMod 409) ^ ((409 - 1) / 2) ≠ 1 from power_409_2), (List.forall_mem_cons.mpr ⟨(show (21 : ZMod 409) ^ ((409 - 1) / 2) ≠ 1 from power_409_2), (List.forall_mem_cons.mpr ⟨(show (21 : ZMod 409) ^ ((409 - 1) / 2) ≠ 1 from power_409_2), (List.forall_mem_cons.mpr ⟨(show (21 : ZMod 409) ^ ((409 - 1) / 3) ≠ 1 from power_409_3), (List.forall_mem_cons.mpr ⟨(show (21 : ZMod 409) ^ ((409 - 1) / 17) ≠ 1 from power_409_17), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 409 (21 : ZMod 409) power_409_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_1637_full : List PowStep := [
  (6, 64),
  (6, 231),
  (4, 1)]

private theorem power_1637_full : (2 : ZMod 1637) ^ 1636 = 1 :=
  trace_power 1637 2 1636 1 trace_1637_full
    (by decide) (by decide) (by decide)

private def trace_1637_2 : List PowStep := [
  (3, 8),
  (3, 382),
  (2, 1636)]

private theorem power_1637_2 : (2 : ZMod 1637) ^ 818 ≠ 1 :=
  trace_power_ne_one 1637 2 818 1636 trace_1637_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_1637_409 : List PowStep := [
  (4, 16)]

private theorem power_1637_409 : (2 : ZMod 1637) ^ 4 ≠ 1 :=
  trace_power_ne_one 1637 2 4 16 trace_1637_409
    (by decide) (by decide) (by decide) (by decide)

theorem prime_1637 : Nat.Prime 1637 := by
  let factors : List Nat := [2, 2, 409]
  have hf : factors.prod = 1637 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_409, by simp⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 1637) ^ ((1637 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1637) ^ ((1637 - 1) / 2) ≠ 1 from power_1637_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1637) ^ ((1637 - 1) / 2) ≠ 1 from power_1637_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 1637) ^ ((1637 - 1) / 409) ≠ 1 from power_1637_409), by simp⟩)⟩)⟩)
  apply lucas_primality 1637 (2 : ZMod 1637) power_1637_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_229_full : List PowStep := [
  (14, 215),
  (4, 1)]

private theorem power_229_full : (6 : ZMod 229) ^ 228 = 1 :=
  trace_power 229 6 228 1 trace_229_full
    (by decide) (by decide) (by decide)

private def trace_229_2 : List PowStep := [
  (7, 98),
  (2, 228)]

private theorem power_229_2 : (6 : ZMod 229) ^ 114 ≠ 1 :=
  trace_power_ne_one 229 6 114 228 trace_229_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_229_3 : List PowStep := [
  (4, 151),
  (12, 134)]

private theorem power_229_3 : (6 : ZMod 229) ^ 76 ≠ 1 :=
  trace_power_ne_one 229 6 76 134 trace_229_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_229_19 : List PowStep := [
  (12, 165)]

private theorem power_229_19 : (6 : ZMod 229) ^ 12 ≠ 1 :=
  trace_power_ne_one 229 6 12 165 trace_229_19
    (by decide) (by decide) (by decide) (by decide)

theorem prime_229 : Nat.Prime 229 := by
  let factors : List Nat := [2, 2, 3, 19]
  have hf : factors.prod = 229 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_19, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (6 : ZMod 229) ^ ((229 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 229) ^ ((229 - 1) / 2) ≠ 1 from power_229_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 229) ^ ((229 - 1) / 2) ≠ 1 from power_229_2), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 229) ^ ((229 - 1) / 3) ≠ 1 from power_229_3), (List.forall_mem_cons.mpr ⟨(show (6 : ZMod 229) ^ ((229 - 1) / 19) ≠ 1 from power_229_19), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 229 (6 : ZMod 229) power_229_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem prime_71 : Nat.Prime 71 := by decide

private def trace_853_full : List PowStep := [
  (3, 8),
  (5, 757),
  (4, 1)]

private theorem power_853_full : (2 : ZMod 853) ^ 852 = 1 :=
  trace_power 853 2 852 1 trace_853_full
    (by decide) (by decide) (by decide)

private def trace_853_2 : List PowStep := [
  (1, 2),
  (10, 795),
  (10, 852)]

private theorem power_853_2 : (2 : ZMod 853) ^ 426 ≠ 1 :=
  trace_power_ne_one 853 2 426 852 trace_853_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_853_3 : List PowStep := [
  (1, 2),
  (1, 563),
  (12, 632)]

private theorem power_853_3 : (2 : ZMod 853) ^ 284 ≠ 1 :=
  trace_power_ne_one 853 2 284 632 trace_853_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_853_71 : List PowStep := [
  (12, 684)]

private theorem power_853_71 : (2 : ZMod 853) ^ 12 ≠ 1 :=
  trace_power_ne_one 853 2 12 684 trace_853_71
    (by decide) (by decide) (by decide) (by decide)

theorem prime_853 : Nat.Prime 853 := by
  let factors : List Nat := [2, 2, 3, 71]
  have hf : factors.prod = 853 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_71, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 853) ^ ((853 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 853) ^ ((853 - 1) / 2) ≠ 1 from power_853_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 853) ^ ((853 - 1) / 2) ≠ 1 from power_853_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 853) ^ ((853 - 1) / 3) ≠ 1 from power_853_3), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 853) ^ ((853 - 1) / 71) ≠ 1 from power_853_71), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 853 (2 : ZMod 853) power_853_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_639533339_full : List PowStep := [
  (2, 4),
  (6, 518104513),
  (1, 122159254),
  (14, 338340564),
  (8, 461375189),
  (1, 364905960),
  (1, 203221123),
  (10, 1)]

private theorem power_639533339_full : (2 : ZMod 639533339) ^ 639533338 = 1 :=
  trace_power 639533339 2 639533338 1 trace_639533339_full
    (by decide) (by decide) (by decide)

private def trace_639533339_2 : List PowStep := [
  (1, 2),
  (3, 524288),
  (0, 290739023),
  (15, 131104910),
  (4, 62728889),
  (0, 211763364),
  (8, 446925292),
  (13, 639533338)]

private theorem power_639533339_2 : (2 : ZMod 639533339) ^ 319766669 ≠ 1 :=
  trace_power_ne_one 639533339 2 319766669 639533338 trace_639533339_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_639533339_229 : List PowStep := [
  (2, 4),
  (10, 615272140),
  (9, 421356568),
  (13, 427885953),
  (1, 560023661),
  (2, 271298491)]

private theorem power_639533339_229 : (2 : ZMod 639533339) ^ 2792722 ≠ 1 :=
  trace_power_ne_one 639533339 2 2792722 271298491 trace_639533339_229
    (by decide) (by decide) (by decide) (by decide)

private def trace_639533339_853 : List PowStep := [
  (11, 2048),
  (7, 418421286),
  (0, 42878818),
  (11, 486480982),
  (2, 256057581)]

private theorem power_639533339_853 : (2 : ZMod 639533339) ^ 749746 ≠ 1 :=
  trace_power_ne_one 639533339 2 749746 256057581 trace_639533339_853
    (by decide) (by decide) (by decide) (by decide)

private def trace_639533339_1637 : List PowStep := [
  (5, 32),
  (15, 59073833),
  (6, 318239802),
  (1, 534791347),
  (2, 248876995)]

private theorem power_639533339_1637 : (2 : ZMod 639533339) ^ 390674 ≠ 1 :=
  trace_power_ne_one 639533339 2 390674 248876995 trace_639533339_1637
    (by decide) (by decide) (by decide) (by decide)

theorem prime_639533339 : Nat.Prime 639533339 := by
  let factors : List Nat := [2, 229, 853, 1637]
  have hf : factors.prod = 639533339 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_229, (List.forall_mem_cons.mpr ⟨prime_853, (List.forall_mem_cons.mpr ⟨prime_1637, by simp⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (2 : ZMod 639533339) ^ ((639533339 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 639533339) ^ ((639533339 - 1) / 2) ≠ 1 from power_639533339_2), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 639533339) ^ ((639533339 - 1) / 229) ≠ 1 from power_639533339_229), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 639533339) ^ ((639533339 - 1) / 853) ≠ 1 from power_639533339_853), (List.forall_mem_cons.mpr ⟨(show (2 : ZMod 639533339) ^ ((639533339 - 1) / 1637) ≠ 1 from power_639533339_1637), by simp⟩)⟩)⟩)⟩)
  apply lucas_primality 639533339 (2 : ZMod 639533339) power_639533339_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_65865678001877903_full : List PowStep := [
  (14, 6103515625),
  (10, 49714088955607834),
  (0, 29783264655931780),
  (0, 58803425563645699),
  (7, 16852790087729705),
  (12, 37617870094920244),
  (3, 8994618634358070),
  (4, 20814136980128200),
  (3, 62949205407553473),
  (1, 59203783134179939),
  (3, 14275770065850360),
  (3, 8537704510709684),
  (8, 43433959607128670),
  (14, 1)]

private theorem power_65865678001877903_full : (5 : ZMod 65865678001877903) ^ 65865678001877902 = 1 :=
  trace_power 65865678001877903 5 65865678001877902 1 trace_65865678001877903_full
    (by decide) (by decide) (by decide)

private def trace_65865678001877903_2 : List PowStep := [
  (7, 78125),
  (5, 57506806652306812),
  (0, 41376488407476446),
  (0, 54614436790736835),
  (3, 15582873565392459),
  (14, 17679944513336428),
  (1, 3042107415912872),
  (10, 40511297818254427),
  (1, 50262081407488025),
  (8, 29829323268635827),
  (9, 32687860450708136),
  (9, 9647066329942654),
  (12, 59008885819339970),
  (7, 65865678001877902)]

private theorem power_65865678001877903_2 : (5 : ZMod 65865678001877903) ^ 32932839000938951 ≠ 1 :=
  trace_power_ne_one 65865678001877903 5 32932839000938951 65865678001877902 trace_65865678001877903_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_65865678001877903_83 : List PowStep := [
  (2, 25),
  (13, 57284035326059365),
  (1, 14651247656979002),
  (11, 51402394271451606),
  (13, 60434120770248014),
  (10, 40401303478680931),
  (4, 64295446428145034),
  (1, 7628523286619542),
  (9, 6713246501241653),
  (4, 14934893779487498),
  (4, 62922329801414354),
  (7, 12108439650369112),
  (10, 46316002665751102)]

private theorem power_65865678001877903_83 : (5 : ZMod 65865678001877903) ^ 793562385564794 ≠ 1 :=
  trace_power_ne_one 65865678001877903 5 793562385564794 46316002665751102 trace_65865678001877903_83
    (by decide) (by decide) (by decide) (by decide)

private def trace_65865678001877903_379 : List PowStep := [
  (9, 1953125),
  (14, 45095700801379161),
  (0, 38095640734331574),
  (15, 60515056213252836),
  (3, 58931433685859231),
  (0, 3149252953698041),
  (1, 14380370799919686),
  (8, 52388735667451923),
  (7, 31581907872013115),
  (2, 3266140316393850),
  (4, 52054151725449514),
  (10, 43783936274874531)]

private theorem power_65865678001877903_379 : (5 : ZMod 65865678001877903) ^ 173788068606538 ≠ 1 :=
  trace_power_ne_one 65865678001877903 5 173788068606538 43783936274874531 trace_65865678001877903_379
    (by decide) (by decide) (by decide) (by decide)

private def trace_65865678001877903_1637 : List PowStep := [
  (2, 25),
  (4, 19645326681927316),
  (9, 3913168907026756),
  (8, 419563847275185),
  (1, 28630063535366704),
  (4, 56655797594495967),
  (10, 7982091751223178),
  (12, 62860760283800497),
  (10, 4865998998029197),
  (13, 44860823647670220),
  (7, 61590809717112550),
  (6, 56641079936670322)]

private theorem power_65865678001877903_1637 : (5 : ZMod 65865678001877903) ^ 40235600489846 ≠ 1 :=
  trace_power_ne_one 65865678001877903 5 40235600489846 56641079936670322 trace_65865678001877903_1637
    (by decide) (by decide) (by decide) (by decide)

private def trace_65865678001877903_639533339 : List PowStep := [
  (6, 15625),
  (2, 2820623742034264),
  (3, 48871129220256727),
  (8, 16088617646272899),
  (1, 44022853474615748),
  (8, 33513450061234789),
  (10, 18968088485270649)]

private theorem power_65865678001877903_639533339 : (5 : ZMod 65865678001877903) ^ 102990218 ≠ 1 :=
  trace_power_ne_one 65865678001877903 5 102990218 18968088485270649 trace_65865678001877903_639533339
    (by decide) (by decide) (by decide) (by decide)

theorem prime_65865678001877903 : Nat.Prime 65865678001877903 := by
  let factors : List Nat := [2, 83, 379, 1637, 639533339]
  have hf : factors.prod = 65865678001877903 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_83, (List.forall_mem_cons.mpr ⟨prime_379, (List.forall_mem_cons.mpr ⟨prime_1637, (List.forall_mem_cons.mpr ⟨prime_639533339, by simp⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (5 : ZMod 65865678001877903) ^ ((65865678001877903 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 65865678001877903) ^ ((65865678001877903 - 1) / 2) ≠ 1 from power_65865678001877903_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 65865678001877903) ^ ((65865678001877903 - 1) / 83) ≠ 1 from power_65865678001877903_83), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 65865678001877903) ^ ((65865678001877903 - 1) / 379) ≠ 1 from power_65865678001877903_379), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 65865678001877903) ^ ((65865678001877903 - 1) / 1637) ≠ 1 from power_65865678001877903_1637), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 65865678001877903) ^ ((65865678001877903 - 1) / 639533339) ≠ 1 from power_65865678001877903_639533339), by simp⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 65865678001877903 (5 : ZMod 65865678001877903) power_65865678001877903_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_13818364434197438864469338081_full : List PowStep := [
  (2, 9),
  (12, 984770902183611232881),
  (10, 12596446258262420570971122539),
  (6, 6013373079058631767301362551),
  (4, 7472161903724485436879936307),
  (8, 6411765538874505385585772480),
  (7, 6459754562886845318727133087),
  (12, 9120529815683458846347129711),
  (15, 5220846285223956177417591636),
  (12, 1886437234314280167008555368),
  (13, 4474036755109480571175560442),
  (7, 524555744109995998299457345),
  (9, 4681862884621048141851485528),
  (5, 6906612351309949603303398410),
  (14, 5112603998534267644417346194),
  (8, 8152258625664711948656211578),
  (7, 11643985796622657375275308179),
  (2, 9072788262601288371685357972),
  (9, 13692602411930922530978190602),
  (5, 12262823178093307119144367918),
  (2, 11973732052671175204970173779),
  (7, 6379790489383530548965005786),
  (14, 11537110112971884460776403123),
  (0, 1)]

private theorem power_13818364434197438864469338081_full : (3 : ZMod 13818364434197438864469338081) ^ 13818364434197438864469338080 = 1 :=
  trace_power 13818364434197438864469338081 3 13818364434197438864469338080 1 trace_13818364434197438864469338081_full
    (by decide) (by decide) (by decide)

private def trace_13818364434197438864469338081_2 : List PowStep := [
  (1, 3),
  (6, 31381059609),
  (5, 7237954386818590318399582276),
  (3, 13402718373407664791149340167),
  (2, 7010042036085959938355337337),
  (4, 12336793362549488461362281727),
  (3, 4008219274052075701249564590),
  (14, 5753971800505551483859975410),
  (7, 9176279723411702349669163029),
  (14, 4102149633039838613723394882),
  (6, 10649380578662279289377282605),
  (11, 3375993396337708788928614156),
  (12, 2425315064956343788793427944),
  (10, 2137690257159955593811335883),
  (15, 12936899612021497549181383642),
  (4, 4658137062062790276173812948),
  (3, 7388014863623266958594661863),
  (9, 2901696624746320249837937994),
  (4, 8676292422495503506343939533),
  (10, 11147805440635279421633713702),
  (9, 735428956798410263315022593),
  (3, 11132134223172545570287568128),
  (15, 1260859393363995662911933059),
  (0, 13818364434197438864469338080)]

private theorem power_13818364434197438864469338081_2 : (3 : ZMod 13818364434197438864469338081) ^ 6909182217098719432234669040 ≠ 1 :=
  trace_power_ne_one 13818364434197438864469338081 3 6909182217098719432234669040 13818364434197438864469338080 trace_13818364434197438864469338081_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_13818364434197438864469338081_5 : List PowStep := [
  (8, 6561),
  (14, 4729600144503398049815677346),
  (14, 7085420474905480256025188320),
  (0, 12078650943931578878364068039),
  (14, 4264280084793279219018460469),
  (7, 5623322501953383616000256866),
  (15, 9845050367966504210852552877),
  (6, 1826678360427168661471407555),
  (5, 10261683629733791425187191901),
  (12, 9426931464382575805465049285),
  (4, 2598988497536901932514961819),
  (11, 12720295886214502532202769565),
  (7, 260175586676158321229518690),
  (9, 12861850517747868121020638167),
  (4, 7986225932371941881493406325),
  (14, 13638261056818929699542092413),
  (3, 9410939446127253418521980745),
  (11, 12496393151814719225894452793),
  (7, 827277734698424783530483313),
  (6, 4552407746075074349532718048),
  (14, 2955222540862682613491674607),
  (6, 694153836874816883066776306),
  (0, 1236319344469036993987267104)]

private theorem power_13818364434197438864469338081_5 : (3 : ZMod 13818364434197438864469338081) ^ 2763672886839487772893867616 ≠ 1 :=
  trace_power_ne_one 13818364434197438864469338081 3 2763672886839487772893867616 1236319344469036993987267104 trace_13818364434197438864469338081_5
    (by decide) (by decide) (by decide) (by decide)

private def trace_13818364434197438864469338081_823 : List PowStep := [
  (13, 1594323),
  (14, 3291014836528682276920607362),
  (3, 6308472844442302776435586832),
  (7, 10070958392044978548315094411),
  (8, 9946594894341867461765371163),
  (8, 1398510122435128853796524203),
  (7, 5688912060539484367032331136),
  (14, 7025164686954433188671008389),
  (13, 8695998603008442701814596966),
  (9, 177558570764698118261074483),
  (9, 12454673513181502265767683890),
  (3, 1703653303783938486715718960),
  (8, 4888000617380104018408080166),
  (14, 10182571199760742458445167908),
  (5, 12032457260559535307619343342),
  (1, 13202442814668619774071314455),
  (3, 8978180551129977492856699409),
  (12, 9241836001525996325221424045),
  (7, 2505391460118300821310770026),
  (2, 6512259595114165664121777531),
  (0, 570363171180057177517864248)]

private theorem power_13818364434197438864469338081_823 : (3 : ZMod 13818364434197438864469338081) ^ 16790236250543668122076960 ≠ 1 :=
  trace_power_ne_one 13818364434197438864469338081 3 16790236250543668122076960 570363171180057177517864248 trace_13818364434197438864469338081_823
    (by decide) (by decide) (by decide) (by decide)

private def trace_13818364434197438864469338081_1593227 : List PowStep := [
  (1, 3),
  (13, 68630377364883),
  (6, 7609269325351490579405976877),
  (2, 11374983810337917037422803229),
  (12, 7099274194976322802038548096),
  (11, 75148684281086399757805112),
  (9, 3623517793516502901398798115),
  (8, 8697426238720052358232810214),
  (15, 2607815355233742944708123496),
  (5, 3313056338523307812547804164),
  (14, 8314049320593930747978251404),
  (5, 11703947348268953898127958737),
  (11, 1625223069757162315976869610),
  (15, 3431342641712895837841559513),
  (8, 4258768977098615392773916346),
  (7, 7346269920723315002668060560),
  (3, 12636366034629803162878776201),
  (10, 6630130951610966011268207104),
  (0, 9233249052774251384923794665)]

private theorem power_13818364434197438864469338081_1593227 : (3 : ZMod 13818364434197438864469338081) ^ 8673192479287282267040 ≠ 1 :=
  trace_power_ne_one 13818364434197438864469338081 3 8673192479287282267040 9233249052774251384923794665 trace_13818364434197438864469338081_1593227
    (by decide) (by decide) (by decide) (by decide)

private def trace_13818364434197438864469338081_65865678001877903 : List PowStep := [
  (3, 27),
  (0, 79766443076872509863361),
  (13, 7608310082675760512433437000),
  (8, 6147467998679698979734732933),
  (13, 11250983929527819103187191017),
  (2, 9542189745429171007173691265),
  (14, 12355991209096219870804905578),
  (10, 8617763932575249144691017398),
  (2, 4547809021354800476213075737),
  (0, 11685553033882782147454259209)]

private theorem power_13818364434197438864469338081_65865678001877903 : (3 : ZMod 13818364434197438864469338081) ^ 209796131360 ≠ 1 :=
  trace_power_ne_one 13818364434197438864469338081 3 209796131360 11685553033882782147454259209 trace_13818364434197438864469338081_65865678001877903
    (by decide) (by decide) (by decide) (by decide)

theorem prime_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 := by
  let factors : List Nat := [2, 2, 2, 2, 2, 5, 823, 1593227, 65865678001877903]
  have hf : factors.prod = 13818364434197438864469338081 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_5, (List.forall_mem_cons.mpr ⟨prime_823, (List.forall_mem_cons.mpr ⟨prime_1593227, (List.forall_mem_cons.mpr ⟨prime_65865678001877903, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / 2) ≠ 1 from power_13818364434197438864469338081_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / 2) ≠ 1 from power_13818364434197438864469338081_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / 2) ≠ 1 from power_13818364434197438864469338081_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / 2) ≠ 1 from power_13818364434197438864469338081_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / 2) ≠ 1 from power_13818364434197438864469338081_2), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / 5) ≠ 1 from power_13818364434197438864469338081_5), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / 823) ≠ 1 from power_13818364434197438864469338081_823), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / 1593227) ≠ 1 from power_13818364434197438864469338081_1593227), (List.forall_mem_cons.mpr ⟨(show (3 : ZMod 13818364434197438864469338081) ^ ((13818364434197438864469338081 - 1) / 65865678001877903) ≠ 1 from power_13818364434197438864469338081_65865678001877903), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 13818364434197438864469338081 (3 : ZMod 13818364434197438864469338081) power_13818364434197438864469338081_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_full : List PowStep := [
  (3, 125),
  (0, 3552713678800500929355621337890625),
  (6, 7655004590256582837831759880035028699545382017496924375072382483157270584848),
  (4, 1529073607188199410183149168738248905581602555356055434634892474431355010581),
  (4, 12301284706844877689472251122113057448755843976851070785641120989993949132946),
  (14, 11958847517414781215061269953450853392437724657183239622145513938599101632571),
  (7, 6333763033519229937480232744617183760288677384776897396116088586793729973950),
  (2, 19577141621140546406115453347575922078242058940758348805705073547085318911838),
  (14, 9458403882487798320989734553303156254010260864667099454899640419026475187093),
  (1, 9107577473661076821685658970173582713612041646245702661643463558467498237606),
  (3, 3790144017414292299573907683648932946391382732421517268482886579952542944303),
  (1, 1985828755570259780477591220750285835580189302113596682743569617406275254678),
  (10, 11002182945649987039072246088824604219068541423759077798964713693363795858217),
  (0, 19147733806758881599273771429250252088559048563967911587232422304799831638984),
  (2, 7013649282038711802352640860150828226913060073931972169896723395637144313821),
  (9, 7968305385463580032146292235048651368006300469800061112993626492638717231385),
  (11, 11407807887146229938213656067958629474834747117764936279872869141834883236830),
  (8, 13777896854708458835980331319073244619640746478316508530560495324217448643299),
  (5, 9036257926491226812667754390463331337676149736936057219326007369931799649259),
  (0, 2242496093322283183249880691717933844681648693069345059688582053818125947203),
  (4, 13143251247562471277748239831026278817064498508278610220033467251065173988347),
  (5, 19892089610898374722219151191961117824954156591960686773809378775366971110692),
  (11, 21486132559747171456370716794948241790034655913773575583202432422811391482439),
  (6, 20448453140214291789484296576729586162118613490594305482575206063405731450512),
  (8, 13246191798445226434479132963975347816511682872356457779059312176322658712523),
  (1, 12464739615718625832554523727207086231490959500634918140410800374504290636121),
  (8, 4945528219670027244589637336847812033691749831762794040936622984559622225431),
  (1, 17270008162749082263149874733279093680131595078605179081369836067898027019703),
  (5, 11969324974846786871647695185550916944604590851467788346707104191238287664973),
  (8, 5905003372224387228846613577227068724287036392824856617263206523973915967561),
  (5, 12704883686463174763359334784411373322834660937612138441603138333735631782629),
  (13, 5517217188276009377578658542007421826968391990017402123511112470792573750024),
  (2, 21557933452595207642763345360774527844456422463976228734958767508658416555701),
  (8, 3594609604481854206906020989070521313082116472571880773980016780044079804617),
  (3, 9978142382581836083394488739391171229827799819935292177051107503295013014865),
  (3, 9608263533402201177314772758552292668627017986940321295441189851709618059978),
  (14, 14892649614528839654169028971139063009499781759254866059744450462017781022802),
  (8, 19048060928032714591417534755946607634654240098947699617078024922613392412787),
  (4, 5057202144798839499450014372260571171482027748388788617262944271947016417803),
  (8, 9579206542913659258240905957342899449291399317339313502305956160548126360531),
  (7, 16306061378945417499547689990469560476726625588866812400965843903745002171320),
  (9, 1943201329826588388270439141265312603161414707756492044047941290472948293150),
  (11, 20161422863521357340736523006175480061239753447882726980318339004137231584219),
  (9, 3456158722108757805166158752147389326097267257793635151814555662475695313921),
  (7, 18205901062977018423198743347807140989506408936725232654902166322973911547001),
  (0, 11969251670545564906427322491981671093730621703182074123151076258052128948308),
  (9, 9061542223363942494619405717243633225630770467232373133371354230755635562274),
  (1, 14938748169776878130809849169493198826524946368436660516023968911503332636423),
  (4, 10490369222805117846589041214555248567797986013574314709671017272084826234648),
  (3, 13859074915942825223780066375404238746394152374296986706583155839500349989276),
  (14, 21252797058633888110669512457827758046735110009970338276828411647506534046872),
  (1, 18075617560161400017265719064587082343539520290825042907816305187579429967267),
  (15, 17455065840341016599016362060421014240668472366741397563567140602202677457893),
  (5, 15136459971889329318676257437087086493381345671803843509103584356611064634950),
  (9, 10610473177882773990001559912042244532022120605293286388691001914180527198299),
  (3, 5051757990388364294045374072784308903399859774183898982473141990546888223579),
  (15, 19103219067921713944291392827692070036145651957329286315305642004821462161904),
  (0, 5709868443893258075976348696661355716898495876243883251619397131511003808859),
  (0, 17220337697351015657950521176323262483320249231368149235373741788599650842711),
  (0, 421743594562400382753388642386256516545992082196004333756405989743524594615),
  (0, 4158865282786404163413953114870269622875596290766033564087307867933865333818),
  (0, 3478517300119284901893091970156912948790432420133812234316178878452092729974),
  (0, 14940766826517323942636479241147756311199852622225275649687664389641784935947),
  (0, 1)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_full : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 21888242871839275222246405745257275088548364400416034343698204186575808495616 = 1 :=
  trace_power 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 21888242871839275222246405745257275088548364400416034343698204186575808495616 1 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_full
    (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_2 : List PowStep := [
  (1, 5),
  (8, 59604644775390625),
  (3, 9086614246629678409901891358980307970763007317620017294639366207294686486377),
  (2, 7122149797049657406560069179679128750064069009214282033263205883947167685589),
  (2, 3116273844467330801829001622792568843079926253117073339408483697909462424626),
  (7, 9584622151981067344174680760542456094210385546162912082661108929439870980748),
  (3, 517373029847386283780060741626053464129344970908342161092808690292186612163),
  (9, 14569735884458382856254784209912830376236225605784403836765118408925324734017),
  (7, 10515933692801596054137274619403467303992730962120133861438972633219469456172),
  (0, 15364255734425713002718835933644000406291089247791499507392333308306132147049),
  (9, 9915302353866463282044221001597139702102547599566625451143944039358989129856),
  (8, 10013671365415589539201407492754203210643547010114855874351378195379236706658),
  (13, 10783696055532049719109712848731009853889929231726391350409941317125095091687),
  (0, 2402354128223672328358869780121422578622443142442801963686561454147809696357),
  (1, 3886134410982702694554336166722418704666193174880187586743526178045498209802),
  (4, 11272276662310496532619612006108119513586372798821762845622598892375354286427),
  (13, 2603510155155449425351324680136310789914599518979895666700542175361390231641),
  (12, 21874273728822463733401318157604561819725490105559641109087200596869146930838),
  (2, 16502609259198323201554641579931238458835997809478122212338335242405916677844),
  (8, 8343872891997277668601868321862574652818926223018918269209044664331295966149),
  (2, 4134476305357831057785045960074432485207368274479980272884084381762189469934),
  (2, 18902839417881785115916266533065687752930047717524368274171973011827260007115),
  (13, 2084194416648000928528537406468776091667240941797815725032282949259973261067),
  (11, 14813525971648781834912506123465838311053330219062308586587401120808795393795),
  (4, 9376517347857831937009618928236940371959486735826044671830336997827458174850),
  (0, 1294007377075685471616421760603917760062792716786573274240018593023678294688),
  (12, 14366811465435179739912877045164387184657053008517704811432583758608568101504),
  (0, 754566290014599858376334434046059585607389134598520802583940160157671647970),
  (10, 6425611171681505176001267956657120053224756614331989312868608837284957809021),
  (12, 17772940573227735660822313500887420407164849853616000784655108386543888319091),
  (2, 18768133358106523373411654634717646896106986213984818118701124029201321608197),
  (14, 19129979934757928616124920877211488417292764770213222532297807244005181690048),
  (9, 12494802654227597455145297345515982409439655412167168111096214354004181857020),
  (4, 16747659364652639747531990691648657637388461381937856284151428599921887086782),
  (1, 10722679947205603560644882634460531018055450310674846622429009641286694866438),
  (9, 751405754761996497287697911178205239224845749818669177867786597867590859340),
  (15, 8720381750765444020246716808803326384476524582097196911534699655030093900312),
  (4, 20710938132140626513949373190327770326956328697392362811499687227769032515796),
  (2, 8688527548647302701724961424360795545182064770166054250650577990793349036634),
  (4, 13163660610909834569616811784312169321574940972830683575230863032866261626959),
  (3, 4240087459284698771200184234856471714831664842049934765271594327660777472651),
  (12, 11307908243200590983912226516199098538677525625234053459875352388865085208733),
  (13, 13305767183019947994369697708435408097155047623286467549698266195193572556896),
  (12, 4031598524059352681220240458485118380885926112118639552555483931584623568936),
  (11, 5193161134101987841005332192047631706719996804743058780668119996728484547841),
  (8, 12884993852127825220611561092387825975427124727324898546348906356907352426900),
  (4, 16278962444712543222161982882950573234696921839554216072953517402982671314135),
  (8, 17898123499280837878048763555213381316685887531033950867536307914915923762881),
  (10, 4593135266042967422011463256484233142601212075001244522796606496438689911128),
  (1, 2369857495604672075885586745501376665292538597775222601363517338362885229667),
  (15, 12055348549749370040492776391518332730517270762405466490330518457489883398286),
  (0, 12118804860518670145098489159991402417888461380160045337181206144932510518417),
  (15, 3018937801257910216515047324755150230061739800647458677846584795504153630758),
  (10, 12432341267527756745256562101780752298590697240126755332407548816141571972251),
  (12, 789170716349317388151285254225649761838141032716085490053900106686664126803),
  (9, 610310806950017018757722104526767371315807778323775703978940537639595320464),
  (15, 8555721953629461299286736829542406442931665950900867472601658309925438163304),
  (8, 19200870435978225707111062059747084165650991997241425080699860725083300967194),
  (0, 13536764371732269273912573961853310557438878140379554347802702086337840854307),
  (0, 12650941915662020058015862023665998998969191525479888727406889100124684769509),
  (0, 197302210312744933010843010704445784068657690384188106020011018676818793232),
  (0, 6837567842312086091520287814181175430087169027974246751610506942214842701774),
  (0, 4419234939496763621076330863786513495701855246241724391626358375488475697872),
  (0, 21888242871839275222246405745257275088548364400416034343698204186575808495616)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 10944121435919637611123202872628637544274182200208017171849102093287904247808 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 10944121435919637611123202872628637544274182200208017171849102093287904247808 21888242871839275222246405745257275088548364400416034343698204186575808495616 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_2
    (by decide) (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_3 : List PowStep := [
  (1, 5),
  (0, 152587890625),
  (2, 8037202955775869412406870020725505882197189478097641211789593127334251249360),
  (1, 4759077888650811600191416150745058974943034103785895283272512891177953737816),
  (6, 20083534627871435841749687621055061600172613281486066539283060074311695928077),
  (15, 8882981302176794031864068783011659468779748786762774419963114200859147083628),
  (7, 10700824145947868989908994395745693132887365871389599192552975633829167659567),
  (11, 17455163149858570078826047586125529188746166889230079692916655500351530318016),
  (10, 13067786389880140130144691076240363650350514260459017027835915247163068827493),
  (0, 19110509570615877128207235541426214179440675413501503463070073214773278531313),
  (6, 13680254874423131903697818103101709717163676191455382319438035725538308106447),
  (5, 5485247783814012597495150941595064306078864788598141094377185993980568785739),
  (14, 3104785637623269615840722315267620988518023742952291485457362413733363791891),
  (0, 7558662710053733421942537363459521464356902844544987956229927985341824509135),
  (0, 6366648251326208753900774143681539080465963960639010277733042050650723456609),
  (13, 20014650870347985135343477106596601534530774785969718304260497263141862005960),
  (14, 4083153129425127162061831924382599934321489267865648637869111667429122186193),
  (8, 9263742128512777146714568649952285847530457540903588848763978830795637529195),
  (1, 6344013339323154033014728387764045357944669873085412326698960847357427747096),
  (10, 8558022844865119638077627924981501131957744949337069734074064113539868510039),
  (12, 1261841679419164339467168399852277422983525985868319356743358901085429287240),
  (1, 19400527002554197651836567543702569353404468062779150528659422563195302964041),
  (14, 20925000018848988413512762665229551135654645260148846412983763303999486062109),
  (7, 10312113056735207384971907968872754251388868859374245589478927735084722648134),
  (8, 16147476773319212586387644364283574922234953933971886721213294725143809343970),
  (0, 12481107998784818395939195452165065233683599914898012013623299213285877858508),
  (8, 9994662305073533838328166993605243662148719951225697239378783889858061410342),
  (0, 14608837679127557210034486450391853661416918570644539546837465700790336750979),
  (7, 2666284556220039598227623710517704982688341364958371286251390969244830573250),
  (2, 409981246203740660144253426326913504477337769191608963534370038466144882674),
  (12, 16686435766589682231678041297031728071713560268699902046960767807198543375102),
  (9, 19982250625625444871144033275129367679392015110702217159236755644046536335648),
  (11, 4473548629398218236794216993903053107958169796449127145639980064816289593000),
  (8, 3904317179796606491103735835026016998709029863280368056198182337815099542388),
  (1, 794321474629928386354204619486880271429860306156827724258318081808589813530),
  (1, 8760920752535850361115102522177012326934108064991332385283947371120211179636),
  (4, 6660307990697341250375496479205603935697381253360499885313793811017282834212),
  (13, 6132325150233198364916733160452578037870533679098582162217655040115581090010),
  (6, 8696818253895699944148394985301138569563824339151934850317310377827538419881),
  (13, 16628393025806841056631888930177925352105743008575405541596400644341075415198),
  (7, 7933163959661848587601256451983449398141396727928853849315576806031326597928),
  (13, 21508172145292717590755536838577060823023080276233767091612665837268746071719),
  (14, 12713307049669866755926929350387280219631819995378645983311335215360277204420),
  (8, 5478301249064402739358097493200258754797202849582162520627531346090253356085),
  (7, 6971089748023471021886456304357954214423781173958739005341167339155108277141),
  (10, 8514465833905029907038019279959083698036650428997569667879184918393841845675),
  (13, 6594101388303362703761970381468022872851759721189513074071250457911596652832),
  (11, 4020852637828133096675405786040468788696373894112042628730739248380294318072),
  (1, 20855221537022127193088122146591185888884662193247679747714405183812803417102),
  (6, 2283152843077603091235486853345679879964409738067385127002594441319017560856),
  (10, 5559312940251109371748016640877469833741805946918249645298069665052066694279),
  (0, 1869212296732750617951441302557997904677501625239391258938261806937271681490),
  (10, 17197388473459246194639603054660687754856646838807556625763681569408124901479),
  (7, 13074846615952684984072223670989585569018304517749537885445010522032505155855),
  (3, 9278675422264973430837298200138508219398934384291853905502840996032880384542),
  (1, 17530118110431457463853336356454118194255506468402432719386294600666666996992),
  (5, 32731794327357592083644034419232168272636089240365817676723289093412795927),
  (0, 21191220957843918668309684578494719913091853688988170905187177989244257268596),
  (0, 2368787508991534596413951697057273526944260286055437404268560086580087225224),
  (0, 15945351209664581495976169035593214991218337414410806935423493143468026708654),
  (0, 2840886268309701182445191370394397404436223560881452801191953251515335955851),
  (0, 7893008526474614989282376550582713669440542763891908783290097886313069160279),
  (0, 18553046819045404058455239539176708534597665700997423782449611735426735463871),
  (0, 4407920970296243842393367215006156084916469457145843978461)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_3 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 7296080957279758407415468581752425029516121466805344781232734728858602831872 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 7296080957279758407415468581752425029516121466805344781232734728858602831872 4407920970296243842393367215006156084916469457145843978461 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_3
    (by decide) (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_13 : List PowStep := [
  (3, 125),
  (11, 173472347597680709441192448139190673828125),
  (8, 1613947510303856046430811018695919681209728106186417237044374132983210108378),
  (15, 563867656146891529615852890788228629064764063887334649368314223079150770690),
  (2, 21243997885910626896547071837290528062587643398944000180504914310070075786784),
  (5, 3118102311133834918705500854083115415519873271538360025484298573409075183279),
  (7, 1133882821743649618996186899589772406620172528377102230215915148036323323024),
  (9, 18459147972046453883160604026651996013072827558555370498043226953012634864477),
  (11, 2346771089321663491824525693693670580071111739854196000612182231472226884195),
  (2, 13185374493861793998637016504061047312315708278850893510328524057686001386258),
  (11, 4251169863506742437449511705470241938791603243944018245362287836721982803275),
  (3, 4114746330838514599095033258808356592779667235177841656907816312419484522092),
  (3, 11099575347460555086704362383885594835294786914505982198781087480602928141011),
  (11, 4558220676065243552733931934887617284108007243177474081801750600801161715110),
  (4, 17828797455254217110345576049978578106691691767616357401025116930850342861766),
  (7, 17397991122560893179567379357591215074151484592471841118059534522626038735073),
  (0, 19958730486942905463692009072554834333634183627212918949188526989905619106946),
  (10, 13001898457075716181932934542452764292701797693459009837408870198105738046444),
  (3, 15219356024984555862843514161938533127835175235252356821454235150490922207035),
  (11, 1563938061077328435750259837060043496486433085939115457515363041334214086648),
  (6, 16679339126251188472516690857073281625766884460120133276840627201863706337358),
  (9, 21802601500559684159507960458080173006512665630079832907432255684650410253415),
  (7, 2778502718023158735103437368240865659586549837769949094997900314211253976218),
  (14, 14492313741608687869382172042957852523600626321338013911426995911813790835846),
  (2, 1508193999395082862957623589683183664408375737575983323079516650633043530493),
  (9, 2359843467273313361019903433571539027531581090720320774048207384879919088688),
  (3, 1745314812771625034305509150778096711009088924284987288150791346360958787127),
  (12, 7154975335513135491044431136094792309067315684670195113921818593488024792331),
  (11, 8215404024583870561143887550650514822467057663943500786869968280747419687860),
  (11, 9842021497962788949340969407450906543021252980077219336750203398624702595365),
  (8, 19075599878938611994800314375693553225261542163936004056388838681455057773605),
  (6, 639357856989860842647745481095984239615208935294246225312247825522143994365),
  (5, 20611683374926519858904547983635308075272728874804844167125210556366221947362),
  (8, 12714339880283023829321787935719276107712052324459412271699642933347687964490),
  (13, 1127693004944226095207690028451486210310469910933009249532551272815520132613),
  (13, 3891094084901227436228992232419760066353942584628876808035330844750671458386),
  (6, 476045114819273150461735885040197171445609031807085256769778005084337818568),
  (12, 7049004479345700269384466449789279974697478057693358781525640842099317739758),
  (10, 8094740849612015579818970378957632333923699301911435839162551469530802305955),
  (7, 7441927450279448797985543464339371721702993696595158696196592173671637735568),
  (15, 2525761240155042405362186629742097664950176610356986458443199670809779028893),
  (8, 2649105202409952903173859063707228657039615120709371052664860591101293102369),
  (4, 14843025552577497946024042629988209020243203437036744813737686878912932581609),
  (6, 9912016389570951404347856931855876268935346561213775844266416593428604393930),
  (11, 12397335546892118562315756606691164181737125910456804902130487697777164599505),
  (1, 12925308026095656789033961327866774211894719314274126916732356148361999236190),
  (14, 17210373205731080789016384305136857987641798169811050366207240343000869583383),
  (13, 8317830741062585482867628680880399007294837481446278570023332595644752642),
  (13, 1299823619342161966726510329951685167219169051536160688777114944739292786484),
  (13, 20800359896241388772185615907591766668432845010275585858999770318169133528053),
  (6, 15966449878413489682026329672157467282012138306280724556301784974021950167469),
  (4, 13396608567763165302199088929400967419591753127002076715639909864113902802488),
  (13, 10136168685282903553721167794787772107048461099083457744725193520631499872978),
  (15, 7831258104251060151361560925806154856405888293193740396140065773705790729897),
  (7, 1729132869424050464683244322522645065218074209713679485018768191212483560191),
  (11, 15469426224440047276552913563216987349638402315738114175993259892171887868219),
  (0, 13245566089625070678008499501013326796952883335628753726067032660326084539241),
  (0, 21642131873848223915063828068675325129097048667796726645291173458006633771251),
  (0, 12354542781590627247388569328459668597862132993920803423750449419845148612746),
  (0, 12404650989235417420723240665736017937972079334016168635011998139180296107880),
  (0, 12184865045055325299463903526609932208633066884116808944578833279923209618574),
  (0, 14572317700299195206903742094417946094383182918455064178255218782755392140090),
  (0, 20846111736645777009767703653665533493788639406277865704073555848150445038125)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_13 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 1683710990141482709403569672712098083734489569262771872592169552813523730432 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 1683710990141482709403569672712098083734489569262771872592169552813523730432 20846111736645777009767703653665533493788639406277865704073555848150445038125 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_13
    (by decide) (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_29 : List PowStep := [
  (1, 5),
  (10, 1490116119384765625),
  (11, 8256342701759641828895219496399674581230902110424998893088311328857076402271),
  (2, 21246274478091776449728612951910660964661227706130709058959736688949900220925),
  (14, 13288031061673966207064163306418527809553457721214349294081916043449397617038),
  (13, 7868381044688160519774751466827837158110605815010785797096232551556798604883),
  (7, 2593172599436332694135729096839139380991982074669237667800681280584676869754),
  (13, 21858353445997513189490663457187574303109929136528967642793054053416733586057),
  (2, 8907277905385383149636172720969396632371057230841984938193033488314956256263),
  (12, 8628449098770850288961439297322563556788807242414407737378811077966515437218),
  (12, 11726744258520248753420676707109729918280869356893393840126611567641122204317),
  (11, 20879320700087174579302331209932693077786073784527580645897806479700496549234),
  (14, 10235481866377499298944003078796939370737687643888003465401260509669727460236),
  (14, 12939026190646806030429020031125083493530891056297050630569662328200974122444),
  (6, 9316572841112039585209948736163083721114834201919665068686224423305390784900),
  (15, 9906847166061216107181196601191912049698445615769728524531751004021895789649),
  (4, 1052515319913844968336742426950663235087518271986382122102779186177241182279),
  (11, 21554139673062048550247129528963170859140555538021215162003145156507359565346),
  (3, 19822949719344943623817267885361671802931711900441311548685109199944533758927),
  (5, 17459209972807599676866955656058963773160140362217727885587061273352241925816),
  (1, 1785129025134815607732532370000436144894281803584747959226574589360247014902),
  (13, 7203051770356146318904915550864118015277997166069196312435412572806973395843),
  (10, 2647859913435777503059552266134004248646588253371760395242777954779934192898),
  (2, 17350828854060351934726105639128137112463926787475909754945869357150505014172),
  (7, 6562242045234594589002011063691536215365996844077160641798284884068016286962),
  (12, 517246339989089106189984802995821484521362639832841982103273486105128064305),
  (6, 9456046527437776494605675201191913447873662047963229755772717802493525644255),
  (10, 1609358330642060986860016629742768934655538738970757913027910874887961861927),
  (10, 12696705338623665828377768156957706358988749636750696225512791241986106188768),
  (12, 4294667008624684953700719144609778394287396594863635685387393789265286339673),
  (5, 19535649600323604394944756942683517546574207945053665531381416650511243819090),
  (6, 8689022289102169855737429548572782883176634985447916285636968220508823255946),
  (11, 16085493675415885291820354780811265602891625453009089370768975994867557388088),
  (5, 1437841576214131144565586611840958596197448065824033192083204833900697510403),
  (1, 16608508821262912293105842733298532440567495129201887890415684484022013571661),
  (3, 4265369425453238767441667863877521619141491403583446389484053260373278734923),
  (12, 12475055088430459882419282910780728158457626300068600121445859286581405538154),
  (15, 11591235093224924157194795811813354588678206049099319029953638969970627185912),
  (9, 12571059606377887137660898749393379252060345669752572085698703133451988107913),
  (10, 20377188649106414168779734265481023142770773190218240268122297438982146850016),
  (11, 12011681146125821177717492281611734378879225449523320115963461685433399271238),
  (14, 1445050082810945793294973911687081650780114451690614443910962844717284698555),
  (11, 15571815796701189625620071961858642822405003467388607328536451888806908188224),
  (14, 15784731159975253659634325335382094976326950721867342458042268885303189531808),
  (9, 19127211080567783302412517653939737926874742218328399385452572008050793501762),
  (6, 535121755674125288256878779203542596872003961727874577926614780476023613906),
  (6, 9088029901858700564729856296122875083102546912747215763507911561624241578113),
  (1, 1037683031237049552859385541499069533109592882879738636166689702870803134039),
  (12, 1484345552043732448820283239642286487870570592013712109960443252052816371229),
  (13, 16878336336730451717584859775909189477058545641407582279459766905362474029629),
  (2, 9235679803653669976657194600895579733662683875388285556246414603234469432820),
  (13, 8066523793075690751932803221877223343669547047426472797941496399642658404960),
  (3, 12965821874820007756551544115837266842970917194924709831206019667770586382285),
  (8, 16985670593879976062500287176660434843231976954465946765066109662700248572420),
  (0, 18521297980410695071610567470895323880522436040072079756738556251002948649159),
  (11, 21208970671169459066957977500651203138967606718322178649614609778549779574673),
  (0, 17924014746687414134656716672848173859799070036740723851613683107131423723534),
  (0, 17966333729845047139143049835538655043633921344536835954713061461504010386427),
  (0, 3553524707391612070532612876182667174730731653478549186744743460404018132482),
  (0, 621525154596101100120356708967676316719033427690598776875324505028423459706),
  (0, 13499349565500463108877547068786575534887045099866230576281731112613882904966),
  (0, 10386009369402860538046910564990750238804555024787124428569499490103643828131),
  (0, 18357710930920482893114740859477755941065533295300174657912055312005893977631)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_29 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 754766995580664662836082956733009485812012565531587391162007040916407189504 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 754766995580664662836082956733009485812012565531587391162007040916407189504 18357710930920482893114740859477755941065533295300174657912055312005893977631 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_29
    (by decide) (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_983 : List PowStep := [
  (12, 244140625),
  (9, 21769372520584044467959299875428796510583705021547138575292169792030209244652),
  (10, 17811636372779352820146680409317042481544500164311631076771114186246792336633),
  (4, 6581333600575946047131186115533096467388487235374085084143021590555869534694),
  (0, 15860122416770237497487089366754367389895303671701038797959126674667774046832),
  (11, 17204337747498456507599748537845007245029957340080280824923323177600041272768),
  (3, 2433438507995067902132055507133128291999989378394398576193726758406707872354),
  (14, 3135148045343802800332752950570242546662921786267467833525997921766970549754),
  (12, 12115088449904486853240214162544000155485209504591505378605993592281092040429),
  (8, 2518561279775844737594916605651927572151338835802231357551312302398290567091),
  (4, 3270029167373405508922679122123569356908635615816629945269009163664938954423),
  (11, 4214419170943821885051660322681041727141533223128821546328560542794820087541),
  (8, 4977965558022140470780063665587749233719473472307248009486578540103681570045),
  (6, 18344592702438434081955511437287743404724061495544875059233227709854284047262),
  (12, 18913930762560870353929547399852973267398442365996777887514716740611733287258),
  (12, 7974073566647672824125677558778667117658296788841049366372800194652612255412),
  (9, 16431183643762941082235162421752475717213009584021574807819529314065319082590),
  (2, 7677920703201094618206586873933188570261196302880207002945021762582446201361),
  (1, 7932141271033037969520076672841145857339787261318960421816888809466913060636),
  (10, 1307848719664647721785438960936459959351050921099417449578317603667128528997),
  (10, 14528725026549779019168106217651433357590056029154386007559699633367821896107),
  (8, 21723653422947773324556466386268532846110574003086722962241428989650854295710),
  (1, 21185785217229842852104212251121161400220616252656893103109862953644949792545),
  (4, 14738682007741711767731899782811094800150817492709658591944256592435608960338),
  (13, 19813106647178285524606179025253991674576613583539708184759247465576277592318),
  (11, 13123046137292158256067729877620196579024431252473590421914863560341246349661),
  (13, 14228767508589356606969041024743386072720357129313321509556295115994433250593),
  (2, 12186273088005128887020121032495929477910713773465629852376500735387387730493),
  (8, 21831609873847048681173653673362302641898062685914170530583860979625403152424),
  (15, 15178645714445256241318748365201391946121415330324634767543024029799398085958),
  (11, 15637600520430110864018948828724905067147391759676659127205808816638712590585),
  (5, 14343582870192808887690912822491177746577477072030815441065903033032845836664),
  (10, 8763081304299315056151119258367113352317419987091966713077710235105913158668),
  (6, 16603452716564814948050832244033390960281662390981735212051655764578340343848),
  (11, 2213549690768929338861092253566066274960457614537137005772780109439750054790),
  (12, 2403755024927938088084739789378813148252274397370782712789070693905900569514),
  (10, 19371651754406168502953774306354730074271189886311202185149930907449681214420),
  (15, 9994678345863861742762129161074109123981205599549613710574164295314997484079),
  (2, 17301534891674219245594421926951416035172013154739904716070694606171648211720),
  (5, 11729276961443492437542022878565805446212226856484471786061170492975243904040),
  (2, 7992691376642088306178701397967270127866880666756988490532118517428706482755),
  (3, 1532336409701494838480099474969642908765472747520078545997681308048643837087),
  (9, 7593503974706520491782496164374941684134677907705095625753828523418095600089),
  (2, 1557354675157779906681727123733617924332002848069413328307976918850950658367),
  (5, 20688710974897126208275606452973520373084964134218183083613378437410541390644),
  (14, 19628458937685448588858265449733883170582157251491129632412175178696217894754),
  (8, 5507655406053363736082973500987766117898374452744043561436563193729309639141),
  (14, 2487339137513575675907150279446030734461791698059327963210044740930870553111),
  (4, 3860055192397960547524997624292616665230906584579690598936653422027281531844),
  (1, 8126659651944159857003304735105304244053203567636643480403973816041831568375),
  (10, 17098928266003843765157356996664944481538831354235953148931253408744972341459),
  (8, 6925357996260140927730552651194845683598459783858313127710156179235279193230),
  (13, 4158988208821633941658913034314508263545712867184542060730975123668569659505),
  (9, 20989367779434789684925398783466170771127469298215891014063418613072894508193),
  (0, 11409166176779972866028558421030391379928574325027892834312769961860121921467),
  (0, 3015082375325203271203436512682389181097247799802728243044859993971507326220),
  (0, 18243285881836197847388589329899914917533664301779162004074865700453826763420),
  (0, 8002237536689292034013948277391287279142336017875235265979166695699722645267),
  (0, 13065105554116266237825386817115367620231093444836302830980299587142825421959),
  (0, 10303430752695128690998158881998023957583470286875849149184506216182555701053),
  (0, 16151937248511612831218790030381502136078900305644383989873770910345603053439)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_983 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 22266778099531307448877320188461114027007491760341845720954429487869591552 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 22266778099531307448877320188461114027007491760341845720954429487869591552 16151937248511612831218790030381502136078900305644383989873770910345603053439 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_983
    (by decide) (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_11003 : List PowStep := [
  (1, 5),
  (2, 3814697265625),
  (0, 12846770360473699295214443875390121596324342403583417197775416350638582526130),
  (3, 17492463644578949475019343346334752165623447139086083176511323207618430182917),
  (11, 11093866345576902199852521991492541979505423431942742789736707922466340658071),
  (2, 9645879557666971911019159642215544705644898539981973535928646833261966391566),
  (7, 4521676271438469187113497783677382930072947507069794145983491263232382737097),
  (5, 6812365910849630047652194483256170181534396721746217076023485025432938343646),
  (1, 7991023084885450759812953693906774323392433814179561213013626680385382509130),
  (4, 10069606322893850751182921463170232074627251395645077156382583694614961181377),
  (0, 4023291273691904002258239201797679368550522870777672002207999606055041872854),
  (2, 15201559193895536930449787553689236007603300108249401970065480667381819792491),
  (14, 15691085318386041877360766850078992401712874399406961746046054656876816515121),
  (14, 16074627871348434635576339793076092542917601740824370760891565151640957615252),
  (8, 16022913702821454240575806452985067182490177726165936537890844189784955283237),
  (10, 13324319548870429290964265907359219013153438541424046534459682015323006705974),
  (8, 9085247654849778102264673149289848653237664303381153229203551932827799471820),
  (4, 17005749062771083886475228267503853488674560799346119886181444893300345414100),
  (5, 7028050931970755760094771562680772684817173876755849157454846351423676639282),
  (0, 17127613281645727260886758131902135756104829215343195073144810385168265317168),
  (15, 5473173410467153866313588830262114314486492081783805721281782761926676488576),
  (9, 21320276282856671449952986480681144574106013712788143116775320507869272450807),
  (10, 21154261553283804419994093660485830342256595204423533202169269402493685700858),
  (14, 15050315921661676193678383353337989130877651126917720344225802850160715305340),
  (5, 16887957655768644766797764462787065159724185543175147389714790220956496165874),
  (6, 1691813747587136417656183599835080006246633094539091909266065673840451039132),
  (5, 2253174427160220657480787723028855976677294876481807917476542820137044894832),
  (1, 20994511413984563086087939055123046376363713682153518021029285115900494597328),
  (15, 7254492971696018842975484943411190923571508022113992922922727134944541352305),
  (10, 3748479116546901348476200128972031121062894477272903563095571879477331231503),
  (12, 19458967238386992694776410899669992682785665152244550737319602304709422885944),
  (8, 14213600908005359190102488656725461992623832225768217074091983771426709331248),
  (12, 1646956024668592381927591162412030401778029653276825346874325298733743055324),
  (1, 3705670737278933170996307986065270843799172641064143570518466536153309742471),
  (1, 13447163279957552224513376962961216591095829135319814489824102743471328172165),
  (7, 9381165038849968751425591972991070012963022759201458453667059570634213538153),
  (14, 3973059536460929703668171616236672257330889423425993873698813717456058067093),
  (8, 594726831748750804670926891164947037012455602166562939134534529230205568707),
  (1, 1938900901141739530762363883120767094532899976490655721500702859004671139132),
  (8, 5806107113791522632032841698719326638118703661639492975869445456261214377499),
  (3, 2200296240380713086276183753228110252507330902672335709184445206757638388515),
  (0, 13478175016381296787242044985552370334694233945226675641125992440176664816682),
  (1, 758870381138458792782160130099611245132835526830447888113079086427193138899),
  (10, 11181126054516022066816779239444566482591252608594212191472455379824592218553),
  (15, 20484488153704635008210792099504007851515988529774434312015813438438193501785),
  (7, 5077593223882720991904118007653433712732865287680458560074117791618143812141),
  (7, 10604183788744626234154021399849664925888417304531814480772303540873388154369),
  (0, 1711446086635506933777959148515765436821531745054322470958055835358149783710),
  (9, 16685545069356427320993301273838372807650682270384269701251772609841686600415),
  (7, 16206785403970271940904368957619411057069107281469538161424363612646801708266),
  (7, 16525037436550161816024471509513818120934903229883070613332765809073841409960),
  (7, 1019042077575233512795072669458095838353596534857191860294965257061207678751),
  (8, 14885721261888220278663203558727760738255405480931680958229164348410497758682),
  (13, 15735987328023941326763533622441513940394971356408847986041743864974882285112),
  (0, 11152079415831477589145017139253568807159099172612047767722186693970970101110),
  (0, 8888414218666999169160716469758136893062596261344836610947568943147787028030),
  (0, 11489997105924485371962784784834941870113863820058674729139630035217915902545),
  (0, 267772275490289433777453471727622807924202884510957394013295188299635194991),
  (0, 19787342070710719110836514952057088529935134873276160724960063536044676764279),
  (0, 19397280769804751527190722810290071512161212158167267491565142287120470218192),
  (0, 8299083658399422953216871473066571686783765754016288837524968026835148283600)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_11003 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 1989297725333025104266691424634851866631679033028813445760083994053967872 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 1989297725333025104266691424634851866631679033028813445760083994053967872 8299083658399422953216871473066571686783765754016288837524968026835148283600 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_11003
    (by decide) (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_237073 : List PowStep := [
  (13, 1220703125),
  (6, 4617877384500652928074809424437679646997916818716800515496493412946613174984),
  (0, 15243598447058510950149627207515928997922313025438855952870538171423408988870),
  (9, 8122125913358298021175377288347567060878559575241491962592917178553942519660),
  (9, 14445767767664835790220017234516408293514183820326701938456612154746512058984),
  (7, 7507823120173338260024472425478320210340170752132020695382853000395905509620),
  (1, 6682333059953815459077052210590965429358804718589931453446060449483876114455),
  (8, 6335673887735797728999944622833555082797597607632486158111161054654750555791),
  (9, 1550096355229914711115580002949791751188375619709828849190115275693553572768),
  (13, 5113650692396643792423370644788901042936038127228099365253907869106099528055),
  (11, 11224415627920589828762166332186006382314687347601300760435046441590290594368),
  (5, 18220268961995185156690353948145430664340445904787502665902266850482493158735),
  (12, 6955185775498834353507753361149412573089437925057658084785586529104314784099),
  (8, 21854031119496693353903710592858622386564256680618961078203069124327498300705),
  (0, 3765031885321627783912345213310010050702068996018016695057665129319691741467),
  (6, 10310253426787695659989643810961263906258320498956172115432008366703012691143),
  (15, 11017164116736431856675443311413260201769691120419370109119096915380417252707),
  (10, 19223616772834979093606815265273884060562089931116701089028294990334926885015),
  (1, 2585060391310918168297050680732041313092546417283332430327355088252346259982),
  (2, 8086127486721890780274074982428958425669502051344365262032669400546689319188),
  (2, 11579293017353284778582446699282559983908776659291946927578838058150740257803),
  (13, 14601848787939811332980891038448093147549819388276939809533448336365560612009),
  (6, 13997314802410820786460587995621648114089187653607541367779070137309065091680),
  (4, 13650293735319304586356642710061048946778661431216391951768036948538946967818),
  (14, 1374099336275458550807801031462616110682048314623556324315397682584898685076),
  (13, 18561365448572043534892703033207863019247837721646294660210552893656351649357),
  (13, 21581989397524856822409894666383682184449183039151942098446032785733981897598),
  (11, 13330403152648839447267956362961950361349425949683539660081812537858249053710),
  (15, 10240723414351713864465281913151586817120561041429223237306173921298658572739),
  (12, 3226390766421486745584668623304752344415206992514006489856793099109461301215),
  (3, 13720808261741434560130680179941085746271672454389929945063778559194587401544),
  (0, 7333328300316088277247235345902770995053314343930159466731950997048816698550),
  (5, 10584347697037449588153771555310007578724760917780011500809073885010067577257),
  (0, 815157513932233713543521551615598433366306132039351749170192707490096511450),
  (11, 10490669588795971132090779422971258554236458320500855904036129066892933308266),
  (12, 13362749030883873580379146778013708726028013985186839463444878000278270508814),
  (4, 12123485641713607818439381930938362568925606812167745904147199485993181513188),
  (15, 20030973994532654680655266670894367725327543137236268891007168869628613140766),
  (10, 16130741886894739370174555215008021306412997445451686952789270560009365145208),
  (0, 19937142978081275078494807749266089217105606819739391802756423711638212321376),
  (6, 10871988713077687463471706417658105361675195439950185602364583344144374901203),
  (15, 19541621208322085145865059802419446826569770681115097977097217048589577944096),
  (1, 91408101429707753369673656994284233341599577285945274098256076958820503529),
  (14, 2108148594294956528217128526229780258418456077548634896427742721242452388432),
  (5, 2856472337641202218404377800488788829770892113816750611284575241470019641650),
  (0, 9783898173182397074881285128306172690004969337331996552635739163630055378305),
  (11, 15420614984384452059131792323025974208236875631910261490341183101340333711258),
  (14, 7657908684603718112499229535989361127990243194709356425279410427898343931392),
  (7, 9866380716097872781000338183129321178214499353914245034344026611309431374582),
  (2, 2811388450948604182359313518289560026896536712749917493584739377555212386138),
  (4, 17330037001171444224518986526299429394684749684679218994990907549292188610444),
  (15, 5949618141178396213074365184881592030098188986542785884087243663940882710289),
  (0, 18626408304882409846513996139199742075517756669711956911945131209654251898915),
  (0, 9174731617258344054863412989217146313999640456667955609455170487020708711403),
  (0, 13523775903613384651648313593517484733199311115992958128676272103904290657431),
  (0, 20198763454297957095454666076929604337902525237927480442786755269376595587195),
  (0, 4294680762770249124365418666176600651155308193737519421054209116701089574647),
  (0, 4514205584393989698686104218689934950812482205270977317434620171283028714583),
  (0, 1135558486015409621676726807058439328573409521523979529600469708688064761941)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_237073 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 92327016875980289709272695521030547926370208334209439049146061283131392 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 92327016875980289709272695521030547926370208334209439049146061283131392 1135558486015409621676726807058439328573409521523979529600469708688064761941 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_237073
    (by decide) (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_405928799 : List PowStep := [
  (2, 25),
  (0, 23283064365386962890625),
  (0, 7495163885505393623034273187115628979572515521304066776979959050081691561461),
  (0, 21009648830092215957608161798189815116587041995525842102414668817247297223533),
  (3, 11313431585377625354024071994119449027215938618443956149984110681951368942336),
  (9, 7634591442350600006893369381811370885878360636813892423519566759465614535505),
  (15, 14753126469623438221105564061052195479294639073639821733984564807991137775105),
  (15, 15910890928196055738495427673152933225099162594097620085935737655772118570357),
  (12, 3406684004624509363647107094740851095648957989410535806564777497709959059372),
  (12, 11152798830083390604660543714522556032997167061154944503681897778350904605070),
  (6, 716787567889801584304103711528251030464556550119703854798717433861488051423),
  (6, 696404656816499404161440287665389445922134784667328901212284844369119060973),
  (15, 8689812745239557078852413927789018481994982002918905074561197669633706625019),
  (4, 17304353960584971766223419699176716890367080347769275677812601901507090516048),
  (15, 18930768011660255280126430383614726915025700897157612940310135596926559212577),
  (15, 5853746841560529258944946397384894563773297491715888291218243654685746793295),
  (1, 6321189977961961140452827903212499344473649762335054702080232985615669655230),
  (8, 17778975217553346249811237248327275923096465284697338037024124283657804589883),
  (4, 17616373819549594103990627952395123770973371407393684385653125048448548262854),
  (3, 19804283860976698010516167990127434803667089469333207554017747335525880574269),
  (10, 1351969295561656779407106590710389727075261737920312491413470253364754978717),
  (10, 4245998792897635759593165746989210640554167274884837822442597436879599572696),
  (2, 1114286154143916537705509677537186828923914858959184790666764112967137897134),
  (5, 900465341878333572738773584213853044462881686817462241795363216157151844237),
  (4, 6447998503129929068290811870565739974436087003154776192605696061816058338372),
  (0, 20350541361831651791189194829106767881341847303562576345823887574123967647920),
  (5, 13374555126213110772046555951983137724963412834991976427717729654075433806601),
  (6, 17968605441066919869359076093333868229547417359162454308611631310143466145302),
  (7, 9350282285920638451662176732355846934564419038756501542393247890154704870709),
  (6, 19238788921159421284100439550214332120918504450140301766331447560439783137704),
  (1, 16516314320827946159568453921106802925784463936638738566054501835769395660280),
  (0, 2545340215247703552700429285308286532693924186306058160161460108873442889915),
  (12, 5700167227615245134689722662791162062697283690202341613075332643852788388262),
  (15, 7113170516504626573531215804171426211713485023904347040364197870641713322498),
  (7, 3593073823327953002106382010077546864417445898427301751328931978315873135559),
  (7, 8796359333780479710494996217888686662508044917724387112592389557273376328025),
  (13, 9989906837484135560701055734647890801856179817248173501806095383183814703999),
  (15, 11243684098404738217677994798306291170960328768288179141619345018707541945710),
  (2, 13678737704082626489719601435357067002106597444944879914234851785822478683797),
  (3, 279162032376712997700546693967190387761403276124301356385637463728042590293),
  (3, 10315633502597835434616225449691668188573523913489142405984293916909367805411),
  (1, 17188183661301849814100392191540907108124975057795239604155906798300702567231),
  (2, 3117467540169099221030926927435098614045452452865937786175622901351403768633),
  (9, 12635076657035208724821496075723108332248796212291999519036188189160429721269),
  (4, 18972743381173146381154217690605143125098011832220910284508588953441513695906),
  (9, 20858885263622733450523560718512520662661684846784141813414260048315025050216),
  (4, 13683676562706931082405216692310834239058539300437561133661740746348651448716),
  (14, 3889943303075813458150423644099399994222074786662849744344466519414515848102),
  (2, 18607733800424790051097582180571944170469297552146742550988086349968571750329),
  (1, 17679289793488514376369598306129299099092436135543833948409724606820311971076),
  (0, 14139927539545159572915653762458085461984277144551926906398294535208882687338),
  (0, 615139435680056525725376910483741240929790328702146850827244823364940263763),
  (0, 1050783198370434611701666391778545024118827031208879239936919601218215836764),
  (0, 62154979253520291890010525961583395538162377901075780634840071011563812590),
  (0, 10141199487723674767708907503109223565765205931536222844165697979114391808055),
  (0, 7770029538425006487151778288297347334474913214873545500283608987804365664920),
  (0, 19321818016159037061311250724021617607548090886696614157910334987366532500238)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_405928799 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 53921384552563552462426805409431605981098090062873401459989056323584 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 53921384552563552462426805409431605981098090062873401459989056323584 19321818016159037061311250724021617607548090886696614157910334987366532500238 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_405928799
    (by decide) (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_1670836401704629 : List PowStep := [
  (8, 390625),
  (2, 21335321719362396876008455392092108010349041058854750716270679997540166795307),
  (6, 21280612148816262372521309179132354819814888062042552274792484997967971797472),
  (15, 6274746173241545625384651886891598545689733895107141544904834602606030008852),
  (10, 7687518274064933194007281365182364824872639408107755900117234176913379258765),
  (4, 14598334816514834268589256183534657601829339206301229723454091167635549628810),
  (8, 19832511456723689331305491230959649346369437671473541074771398937870716243609),
  (13, 1799153986064547343501314350612164194122035883536448380918005818256071817422),
  (3, 3875392122234190376659434346338224983269009029934866513008850317779098624746),
  (3, 10808604371522630249338881801188450411603779192774455892552704260469172527256),
  (14, 1770397524097473417662654392757662056745212927149529673704124824378968972553),
  (14, 6142945470462961955364463156434622147431408352143342420872763242922902473944),
  (8, 14145502130757746398187704867113357761752705027088125730439381177436603550414),
  (0, 7746881953287331001839868693013075036639831944691976436935129163913875887584),
  (0, 12930464472931373328867401426486328288657214960086815464115023920279845753125),
  (1, 15237466739784192135931648353134317567775457633571361264672082286015004516719),
  (5, 8502131374606419514838405334001647206146806701003642212469034956338605193907),
  (9, 10530552334606765681916311716486458780249303098964907385538925178081161358495),
  (2, 15032095042341643837824976775640757012564884217781091665668117782432655981296),
  (8, 16332841269173146963819646611258135569045547379356020660157711547875940278960),
  (9, 13545259300290756922960829646249538763242844711121973890169630120473388092617),
  (10, 3521823580676800807413860310101374176392070340524012565937094874710999251972),
  (14, 4552870678430124068532740540332753819070676444866602338864631024575987330309),
  (6, 2155568345463972459299712609838538466264846568500261107823496391011892065117),
  (3, 21685611314307796904264203196480975928371766723815323126794715424259658588617),
  (5, 18473710259807278167769446119767699081964223741896340118812102171092522346679),
  (8, 4890270162155930675216656975955999646394250559827647992750041169054030184837),
  (15, 6477748482186572587018752968684498921040854679539139671956620835029388263113),
  (14, 14676779354522384384314176033334734248223787334082313068155996783332226567739),
  (5, 3372956916724561700142013285373233961283676083499036868975438499010132591178),
  (11, 11556464554186566427387263998269327037855556039513562802207885075216377868510),
  (10, 1821843912978827055431096577471885879733808947407529419651201597299618066505),
  (12, 8491119658505951056981031491909856876032780549255129408596364041613797233333),
  (4, 11427037195450852214990492162614298310081318124957100061469981145293494223539),
  (12, 12036808699134823681153531216893738676575334360474507411509240115252893328506),
  (5, 3866392155792504829065449265886696387817417254556383324974605728670351630825),
  (15, 16225496598723883362695513277210064741315052301289290236578866875528802601330),
  (8, 6001735687062042196082317190322357839320434792649297072031383726662526147942),
  (0, 8174206465146135901338583165821714053008919897378255208845348364124155414815),
  (15, 6770568129093154653450160927198769615247965855412548624218409630066964011430),
  (0, 506364673800712017543000918308423907188713485276428135956114886310513451861),
  (12, 2060033498783531132760381914171291444605519296759016444700657592687980623344),
  (10, 7338445271900934790027295341397218553359639311722893157037602023766299429722),
  (3, 4597167518899693073744014078836088562737004227101656820805080091319315095913),
  (0, 2057328670423663547104618328236130229771686956178942541324157761884444049460),
  (0, 11376407270599110799519566028854375760183108238084418619384558606519016389115),
  (0, 20024039413756401164017000949941597085491209210768812774053446205946542625691),
  (0, 11485480349727003116195992674174023521224476319041417224394600682928358204164),
  (0, 301519919156509197330537435189198310540715209529085122330191057661857949726),
  (0, 3035610120098432297197753239199019327465362446612004704870821472777999094596),
  (0, 19643034808648967981397807206080768497060516784825884862247505212574391305991)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_1670836401704629 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 13100171177446423556613374118717413492986637444144570673659904 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 13100171177446423556613374118717413492986637444144570673659904 19643034808648967981397807206080768497060516784825884862247505212574391305991 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_1670836401704629
    (by decide) (by decide) (by decide) (by decide)

private def trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_13818364434197438864469338081 : List PowStep := [
  (1, 5),
  (1, 762939453125),
  (5, 16679605073524263215315597543264242298511753666208901431889563593310334287109),
  (7, 4143393628247327952794998335389991651209435833262864673621932424042388996863),
  (4, 21083409368753843221090276215891518095426795865009070350032142640422297228205),
  (13, 15432803337989118749689295629187064900908605853259335606853042898231157376941),
  (13, 17310877544306517700614940269423541408673381667626194105356231945487182557561),
  (11, 16592823852343488524616838154930964535127012570481074339214891282162862150430),
  (3, 6422842122618404410085955316550986678835689788297550843809738805842612475736),
  (2, 19180994098283924367490216878185825339155702287438864613282866487885991197309),
  (3, 9848082726488869283708227208437458351606250096403942175718327737256658031320),
  (2, 17847786436791873217522761641900589889226011747198144710240745105833003974474),
  (5, 21095626667306148037546728707033520163160156881569290420788343159781103645077),
  (1, 3214906748774053669473540520819532251390834469138825537000733393184774403896),
  (4, 8201967001817520999393107536185302626746148316005430480900496575340332552906),
  (15, 3447059202413525369827912636201479613111550041885638671730022666427076273896),
  (11, 20191234716667627988637675775573625135801544680462242295542427551792164298477),
  (3, 3716337400421170337055173215228454731898851271388207283785571522123169076708),
  (12, 2222678319985678112737830774905516245760043912156582793835001179147313403741),
  (4, 8984305933163211755657766009864175939289811781309055183184403370370753943215),
  (14, 6596402040120610967507408157707226764732808801517970420309652137569553450459),
  (3, 13953885168993263974000374082086229643611856434493500165157423139819138954081),
  (14, 7715765728571903433628511734962198106599525120708349356674355488049991225085),
  (9, 19165192908110889473783155850911080326760857399400220796198717319245819619112),
  (12, 14897969706482419120061631509814945759015640563803603740424913469400579505128),
  (4, 1698712277146630728027024699103969810661495626011969743792714844302651988018),
  (0, 4047543528616187781725805844241432729579347176217727891459284395223896098057),
  (8, 18169212040897324722508280624618759234575902297340680214986826029768342551643),
  (12, 10218152470283015430909219229429677763174898092225443572080526209768546164850),
  (12, 12807292871920565143342213085624202400382808577692842208774331234114404823906),
  (2, 737658796152552839691527512634680521413566950973780480339677551371910030554),
  (5, 17119303073764597678909296258621010220939745072766199536173059668894968273064),
  (1, 17801088726352043651052775946842239942232230096643786776962728822781195103422),
  (15, 16396691014163678362074761788426770985134934517581268310236628263713517590642),
  (0, 12615062912329858076145221858245793645208586507948395002608337500809739939147),
  (0, 11574130028895582436118472461298847716114387725984284838523197721467336585475),
  (0, 13455100767135518924539514976194810295462072524210138771339122927048850998705),
  (0, 35670862350301790266763722062901034075519296819165265938146095067521107483),
  (0, 2790271347328208494757476644684380552948291706959809559893173930947501808723),
  (0, 14722090250698929372886103857866496426244941466151919511517028502719623824311),
  (0, 7740382856488830440021062471495669005558519249383073335662966997885018076746)]

private theorem power_21888242871839275222246405745257275088548364400416034343698204186575808495617_13818364434197438864469338081 : (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ 1583996642733683218748855262055434666238317428736 ≠ 1 :=
  trace_power_ne_one 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 1583996642733683218748855262055434666238317428736 7740382856488830440021062471495669005558519249383073335662966997885018076746 trace_21888242871839275222246405745257275088548364400416034343698204186575808495617_13818364434197438864469338081
    (by decide) (by decide) (by decide) (by decide)

theorem prime_21888242871839275222246405745257275088548364400416034343698204186575808495617 : Nat.Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617 := by
  let factors : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 13, 29, 983, 11003, 237073, 405928799, 1670836401704629, 13818364434197438864469338081]
  have hf : factors.prod = 21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1 := by decide
  have hpr : ∀ q ∈ factors, Nat.Prime q := (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_2, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_3, (List.forall_mem_cons.mpr ⟨prime_13, (List.forall_mem_cons.mpr ⟨prime_29, (List.forall_mem_cons.mpr ⟨prime_983, (List.forall_mem_cons.mpr ⟨prime_11003, (List.forall_mem_cons.mpr ⟨prime_237073, (List.forall_mem_cons.mpr ⟨prime_405928799, (List.forall_mem_cons.mpr ⟨prime_1670836401704629, (List.forall_mem_cons.mpr ⟨prime_13818364434197438864469338081, by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have hn : ∀ q ∈ factors, (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / q) ≠ 1 := (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 2) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_2), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 3) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_3), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 3) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_3), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 13) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_13), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 29) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_29), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 983) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_983), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 11003) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_11003), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 237073) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_237073), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 405928799) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_405928799), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 1670836401704629) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_1670836401704629), (List.forall_mem_cons.mpr ⟨(show (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) ^ ((21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) / 13818364434197438864469338081) ≠ 1 from power_21888242871839275222246405745257275088548364400416034343698204186575808495617_13818364434197438864469338081), by simp⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  apply lucas_primality 21888242871839275222246405745257275088548364400416034343698204186575808495617 (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617) power_21888242871839275222246405745257275088548364400416034343698204186575808495617_full
  intro q hq hd
  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))

theorem secpBase_prime : Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 := prime_115792089237316195423570985008687907853269984665640564039457584007908834671663

theorem secpScalar_prime : Nat.Prime 115792089237316195423570985008687907852837564279074904382605163141518161494337 := prime_115792089237316195423570985008687907852837564279074904382605163141518161494337

theorem bn254Scalar_prime : Nat.Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617 := prime_21888242871839275222246405745257275088548364400416034343698204186575808495617

end Witgen.PrimeCertificates
