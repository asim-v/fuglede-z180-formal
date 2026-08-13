import Fuglede.K242CompactPremises0
import Fuglede.K242CompactPremises1
import Fuglede.K242CompactPremises2
import Fuglede.K242CompactPremises3
import Fuglede.K242CompactPremises4
import Fuglede.K242CompactPremises5
import Fuglede.K242CompactPremises6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Sharded compact adapter for pinned k=242 base certificate.
SMT SHA-256: `8ef32ff1e169a1bd2c3f7dbe07c739993639ee87ab78d35813519eaf65f7bab3`.
Core-index SHA-256: `ac5b4df4ed85709474c11538854fbeee0a713b38e531a02f9cfd484e93a5d57b`.
-/

namespace Fuglede

def K242CompactShardedRawCertificate : Prop :=
  ∀ (a : Fin 2 → Fin 32 → Int)
    (z : Fin 2 → Fin 32 → Prop),
    -- core premise 0; source assertion 0
    ((a 0 0) = 242) →
    -- core premise 1; source assertion 7
    ((a 0 3) ≥ 0) →
    -- core premise 2; source assertion 125
    (((a 0 0) + (a 0 16)) ≥ 306) →
    -- core premise 3; source assertion 131
    (((a 0 0) + (a 0 1) + (a 0 4) + (a 0 5) + (a 0 8) + (a 0 9) + (a 0 12) + (a 0 13)) ≥ 1782) →
    -- core premise 4; source assertion 133
    (((a 0 0) + (a 0 4) + (a 0 8) + (a 0 12)) ≥ 902) →
    -- core premise 5; source assertion 137
    (((a 0 0) + (a 0 2) + (a 0 8) + (a 0 10)) ≥ 550) →
    -- core premise 6; source assertion 139
    (((a 0 0) + (a 0 1) + (a 0 8) + (a 0 9)) ≥ 396) →
    -- core premise 7; source assertion 163
    (((2 * (a 0 0)) + ((-2) * (a 0 1)) + ((-1) * (a 0 2)) + (1 * (a 0 3)) + (2 * (a 0 4)) + ((-2) * (a 0 5)) + ((-1) * (a 0 6)) + (1 * (a 0 7)) + (2 * (a 0 8)) + ((-2) * (a 0 9)) + ((-1) * (a 0 10)) + (1 * (a 0 11)) + (2 * (a 0 12)) + ((-2) * (a 0 13)) + ((-1) * (a 0 14)) + (1 * (a 0 15)) + (2 * (a 0 16)) + ((-2) * (a 0 17)) + ((-1) * (a 0 18)) + (1 * (a 0 19)) + (2 * (a 0 20)) + ((-2) * (a 0 21)) + ((-1) * (a 0 22)) + (1 * (a 0 23)) + (2 * (a 0 24)) + ((-2) * (a 0 25)) + ((-1) * (a 0 26)) + (1 * (a 0 27)) + (2 * (a 0 28)) + ((-2) * (a 0 29)) + ((-1) * (a 0 30)) + (1 * (a 0 31))) ≥ 0) →
    -- core premise 8; source assertion 167
    (((4 * (a 0 0)) + ((-4) * (a 0 1)) + (4 * (a 0 2)) + ((-4) * (a 0 3)) + ((-1) * (a 0 4)) + (1 * (a 0 5)) + ((-1) * (a 0 6)) + (1 * (a 0 7)) + (4 * (a 0 8)) + ((-4) * (a 0 9)) + (4 * (a 0 10)) + ((-4) * (a 0 11)) + ((-1) * (a 0 12)) + (1 * (a 0 13)) + ((-1) * (a 0 14)) + (1 * (a 0 15)) + (4 * (a 0 16)) + ((-4) * (a 0 17)) + (4 * (a 0 18)) + ((-4) * (a 0 19)) + ((-1) * (a 0 20)) + (1 * (a 0 21)) + ((-1) * (a 0 22)) + (1 * (a 0 23)) + (4 * (a 0 24)) + ((-4) * (a 0 25)) + (4 * (a 0 26)) + ((-4) * (a 0 27)) + ((-1) * (a 0 28)) + (1 * (a 0 29)) + ((-1) * (a 0 30)) + (1 * (a 0 31))) ≥ 0) →
    -- core premise 9; source assertion 169
    (((8 * (a 0 0)) + (8 * (a 0 1)) + ((-4) * (a 0 2)) + ((-4) * (a 0 3)) + ((-2) * (a 0 4)) + ((-2) * (a 0 5)) + (1 * (a 0 6)) + (1 * (a 0 7)) + (8 * (a 0 8)) + (8 * (a 0 9)) + ((-4) * (a 0 10)) + ((-4) * (a 0 11)) + ((-2) * (a 0 12)) + ((-2) * (a 0 13)) + (1 * (a 0 14)) + (1 * (a 0 15)) + (8 * (a 0 16)) + (8 * (a 0 17)) + ((-4) * (a 0 18)) + ((-4) * (a 0 19)) + ((-2) * (a 0 20)) + ((-2) * (a 0 21)) + (1 * (a 0 22)) + (1 * (a 0 23)) + (8 * (a 0 24)) + (8 * (a 0 25)) + ((-4) * (a 0 26)) + ((-4) * (a 0 27)) + ((-2) * (a 0 28)) + ((-2) * (a 0 29)) + (1 * (a 0 30)) + (1 * (a 0 31))) ≥ 0) →
    -- core premise 10; source assertion 171
    (((8 * (a 0 0)) + ((-8) * (a 0 1)) + ((-4) * (a 0 2)) + (4 * (a 0 3)) + ((-2) * (a 0 4)) + (2 * (a 0 5)) + (1 * (a 0 6)) + ((-1) * (a 0 7)) + (8 * (a 0 8)) + ((-8) * (a 0 9)) + ((-4) * (a 0 10)) + (4 * (a 0 11)) + ((-2) * (a 0 12)) + (2 * (a 0 13)) + (1 * (a 0 14)) + ((-1) * (a 0 15)) + (8 * (a 0 16)) + ((-8) * (a 0 17)) + ((-4) * (a 0 18)) + (4 * (a 0 19)) + ((-2) * (a 0 20)) + (2 * (a 0 21)) + (1 * (a 0 22)) + ((-1) * (a 0 23)) + (8 * (a 0 24)) + ((-8) * (a 0 25)) + ((-4) * (a 0 26)) + (4 * (a 0 27)) + ((-2) * (a 0 28)) + (2 * (a 0 29)) + (1 * (a 0 30)) + ((-1) * (a 0 31))) ≥ 0) →
    -- core premise 11; source assertion 175
    (((6 * (a 0 0)) + ((-6) * (a 0 1)) + (6 * (a 0 2)) + ((-6) * (a 0 3)) + (6 * (a 0 4)) + ((-6) * (a 0 5)) + (6 * (a 0 6)) + ((-6) * (a 0 7)) + ((-1) * (a 0 8)) + (1 * (a 0 9)) + ((-1) * (a 0 10)) + (1 * (a 0 11)) + ((-1) * (a 0 12)) + (1 * (a 0 13)) + ((-1) * (a 0 14)) + (1 * (a 0 15)) + (6 * (a 0 16)) + ((-6) * (a 0 17)) + (6 * (a 0 18)) + ((-6) * (a 0 19)) + (6 * (a 0 20)) + ((-6) * (a 0 21)) + (6 * (a 0 22)) + ((-6) * (a 0 23)) + ((-1) * (a 0 24)) + (1 * (a 0 25)) + ((-1) * (a 0 26)) + (1 * (a 0 27)) + ((-1) * (a 0 28)) + (1 * (a 0 29)) + ((-1) * (a 0 30)) + (1 * (a 0 31))) ≥ 0) →
    -- core premise 12; source assertion 177
    (((12 * (a 0 0)) + (12 * (a 0 1)) + ((-6) * (a 0 2)) + ((-6) * (a 0 3)) + (12 * (a 0 4)) + (12 * (a 0 5)) + ((-6) * (a 0 6)) + ((-6) * (a 0 7)) + ((-2) * (a 0 8)) + ((-2) * (a 0 9)) + (1 * (a 0 10)) + (1 * (a 0 11)) + ((-2) * (a 0 12)) + ((-2) * (a 0 13)) + (1 * (a 0 14)) + (1 * (a 0 15)) + (12 * (a 0 16)) + (12 * (a 0 17)) + ((-6) * (a 0 18)) + ((-6) * (a 0 19)) + (12 * (a 0 20)) + (12 * (a 0 21)) + ((-6) * (a 0 22)) + ((-6) * (a 0 23)) + ((-2) * (a 0 24)) + ((-2) * (a 0 25)) + (1 * (a 0 26)) + (1 * (a 0 27)) + ((-2) * (a 0 28)) + ((-2) * (a 0 29)) + (1 * (a 0 30)) + (1 * (a 0 31))) ≥ 0) →
    -- core premise 13; source assertion 179
    (((12 * (a 0 0)) + ((-12) * (a 0 1)) + ((-6) * (a 0 2)) + (6 * (a 0 3)) + (12 * (a 0 4)) + ((-12) * (a 0 5)) + ((-6) * (a 0 6)) + (6 * (a 0 7)) + ((-2) * (a 0 8)) + (2 * (a 0 9)) + (1 * (a 0 10)) + ((-1) * (a 0 11)) + ((-2) * (a 0 12)) + (2 * (a 0 13)) + (1 * (a 0 14)) + ((-1) * (a 0 15)) + (12 * (a 0 16)) + ((-12) * (a 0 17)) + ((-6) * (a 0 18)) + (6 * (a 0 19)) + (12 * (a 0 20)) + ((-12) * (a 0 21)) + ((-6) * (a 0 22)) + (6 * (a 0 23)) + ((-2) * (a 0 24)) + (2 * (a 0 25)) + (1 * (a 0 26)) + ((-1) * (a 0 27)) + ((-2) * (a 0 28)) + (2 * (a 0 29)) + (1 * (a 0 30)) + ((-1) * (a 0 31))) ≥ 0) →
    -- core premise 14; source assertion 195
    (((20 * (a 0 0)) + ((-20) * (a 0 1)) + ((-10) * (a 0 2)) + (10 * (a 0 3)) + (20 * (a 0 4)) + ((-20) * (a 0 5)) + ((-10) * (a 0 6)) + (10 * (a 0 7)) + (20 * (a 0 8)) + ((-20) * (a 0 9)) + ((-10) * (a 0 10)) + (10 * (a 0 11)) + (20 * (a 0 12)) + ((-20) * (a 0 13)) + ((-10) * (a 0 14)) + (10 * (a 0 15)) + ((-2) * (a 0 16)) + (2 * (a 0 17)) + (1 * (a 0 18)) + ((-1) * (a 0 19)) + ((-2) * (a 0 20)) + (2 * (a 0 21)) + (1 * (a 0 22)) + ((-1) * (a 0 23)) + ((-2) * (a 0 24)) + (2 * (a 0 25)) + (1 * (a 0 26)) + ((-1) * (a 0 27)) + ((-2) * (a 0 28)) + (2 * (a 0 29)) + (1 * (a 0 30)) + ((-1) * (a 0 31))) ≥ 0) →
    -- core premise 15; source assertion 199
    (((40 * (a 0 0)) + ((-40) * (a 0 1)) + (40 * (a 0 2)) + ((-40) * (a 0 3)) + ((-10) * (a 0 4)) + (10 * (a 0 5)) + ((-10) * (a 0 6)) + (10 * (a 0 7)) + (40 * (a 0 8)) + ((-40) * (a 0 9)) + (40 * (a 0 10)) + ((-40) * (a 0 11)) + ((-10) * (a 0 12)) + (10 * (a 0 13)) + ((-10) * (a 0 14)) + (10 * (a 0 15)) + ((-4) * (a 0 16)) + (4 * (a 0 17)) + ((-4) * (a 0 18)) + (4 * (a 0 19)) + (1 * (a 0 20)) + ((-1) * (a 0 21)) + (1 * (a 0 22)) + ((-1) * (a 0 23)) + ((-4) * (a 0 24)) + (4 * (a 0 25)) + ((-4) * (a 0 26)) + (4 * (a 0 27)) + (1 * (a 0 28)) + ((-1) * (a 0 29)) + (1 * (a 0 30)) + ((-1) * (a 0 31))) ≥ 0) →
    -- core premise 16; source assertion 201
    (((80 * (a 0 0)) + (80 * (a 0 1)) + ((-40) * (a 0 2)) + ((-40) * (a 0 3)) + ((-20) * (a 0 4)) + ((-20) * (a 0 5)) + (10 * (a 0 6)) + (10 * (a 0 7)) + (80 * (a 0 8)) + (80 * (a 0 9)) + ((-40) * (a 0 10)) + ((-40) * (a 0 11)) + ((-20) * (a 0 12)) + ((-20) * (a 0 13)) + (10 * (a 0 14)) + (10 * (a 0 15)) + ((-8) * (a 0 16)) + ((-8) * (a 0 17)) + (4 * (a 0 18)) + (4 * (a 0 19)) + (2 * (a 0 20)) + (2 * (a 0 21)) + ((-1) * (a 0 22)) + ((-1) * (a 0 23)) + ((-8) * (a 0 24)) + ((-8) * (a 0 25)) + (4 * (a 0 26)) + (4 * (a 0 27)) + (2 * (a 0 28)) + (2 * (a 0 29)) + ((-1) * (a 0 30)) + ((-1) * (a 0 31))) ≥ 0) →
    -- core premise 17; source assertion 203
    (((80 * (a 0 0)) + ((-80) * (a 0 1)) + ((-40) * (a 0 2)) + (40 * (a 0 3)) + ((-20) * (a 0 4)) + (20 * (a 0 5)) + (10 * (a 0 6)) + ((-10) * (a 0 7)) + (80 * (a 0 8)) + ((-80) * (a 0 9)) + ((-40) * (a 0 10)) + (40 * (a 0 11)) + ((-20) * (a 0 12)) + (20 * (a 0 13)) + (10 * (a 0 14)) + ((-10) * (a 0 15)) + ((-8) * (a 0 16)) + (8 * (a 0 17)) + (4 * (a 0 18)) + ((-4) * (a 0 19)) + (2 * (a 0 20)) + ((-2) * (a 0 21)) + ((-1) * (a 0 22)) + (1 * (a 0 23)) + ((-8) * (a 0 24)) + (8 * (a 0 25)) + (4 * (a 0 26)) + ((-4) * (a 0 27)) + (2 * (a 0 28)) + ((-2) * (a 0 29)) + ((-1) * (a 0 30)) + (1 * (a 0 31))) ≥ 0) →
    -- core premise 18; source assertion 207
    (((60 * (a 0 0)) + ((-60) * (a 0 1)) + (60 * (a 0 2)) + ((-60) * (a 0 3)) + (60 * (a 0 4)) + ((-60) * (a 0 5)) + (60 * (a 0 6)) + ((-60) * (a 0 7)) + ((-10) * (a 0 8)) + (10 * (a 0 9)) + ((-10) * (a 0 10)) + (10 * (a 0 11)) + ((-10) * (a 0 12)) + (10 * (a 0 13)) + ((-10) * (a 0 14)) + (10 * (a 0 15)) + ((-6) * (a 0 16)) + (6 * (a 0 17)) + ((-6) * (a 0 18)) + (6 * (a 0 19)) + ((-6) * (a 0 20)) + (6 * (a 0 21)) + ((-6) * (a 0 22)) + (6 * (a 0 23)) + (1 * (a 0 24)) + ((-1) * (a 0 25)) + (1 * (a 0 26)) + ((-1) * (a 0 27)) + (1 * (a 0 28)) + ((-1) * (a 0 29)) + (1 * (a 0 30)) + ((-1) * (a 0 31))) ≥ 0) →
    -- core premise 19; source assertion 209
    (((120 * (a 0 0)) + (120 * (a 0 1)) + ((-60) * (a 0 2)) + ((-60) * (a 0 3)) + (120 * (a 0 4)) + (120 * (a 0 5)) + ((-60) * (a 0 6)) + ((-60) * (a 0 7)) + ((-20) * (a 0 8)) + ((-20) * (a 0 9)) + (10 * (a 0 10)) + (10 * (a 0 11)) + ((-20) * (a 0 12)) + ((-20) * (a 0 13)) + (10 * (a 0 14)) + (10 * (a 0 15)) + ((-12) * (a 0 16)) + ((-12) * (a 0 17)) + (6 * (a 0 18)) + (6 * (a 0 19)) + ((-12) * (a 0 20)) + ((-12) * (a 0 21)) + (6 * (a 0 22)) + (6 * (a 0 23)) + (2 * (a 0 24)) + (2 * (a 0 25)) + ((-1) * (a 0 26)) + ((-1) * (a 0 27)) + (2 * (a 0 28)) + (2 * (a 0 29)) + ((-1) * (a 0 30)) + ((-1) * (a 0 31))) ≥ 0) →
    -- core premise 20; source assertion 211
    (((120 * (a 0 0)) + ((-120) * (a 0 1)) + ((-60) * (a 0 2)) + (60 * (a 0 3)) + (120 * (a 0 4)) + ((-120) * (a 0 5)) + ((-60) * (a 0 6)) + (60 * (a 0 7)) + ((-20) * (a 0 8)) + (20 * (a 0 9)) + (10 * (a 0 10)) + ((-10) * (a 0 11)) + ((-20) * (a 0 12)) + (20 * (a 0 13)) + (10 * (a 0 14)) + ((-10) * (a 0 15)) + ((-12) * (a 0 16)) + (12 * (a 0 17)) + (6 * (a 0 18)) + ((-6) * (a 0 19)) + ((-12) * (a 0 20)) + (12 * (a 0 21)) + (6 * (a 0 22)) + ((-6) * (a 0 23)) + (2 * (a 0 24)) + ((-2) * (a 0 25)) + ((-1) * (a 0 26)) + (1 * (a 0 27)) + (2 * (a 0 28)) + ((-2) * (a 0 29)) + ((-1) * (a 0 30)) + (1 * (a 0 31))) ≥ 0) →
    -- core premise 21; source assertion 221
    (¬ (z 0 2)) →
    -- core premise 22; source assertion 222
    ((a 0 2) = 0) →
    -- core premise 23; source assertion 224
    ((a 0 4) = 0) →
    -- core premise 24; source assertion 225
    (¬ (z 0 8)) →
    -- core premise 25; source assertion 226
    ((a 0 8) = 0) →
    -- core premise 26; source assertion 235
    (((z 0 6) ∧ (z 0 10) ∧ (z 0 18)) → (z 0 2)) →
    -- core premise 27; source assertion 239
    (((z 0 9) ∧ (z 0 10) ∧ (z 0 12) ∧ (z 0 24)) → (z 0 8)) →
    -- core premise 28; source assertion 240
    ((a 1 0) = 242) →
    -- core premise 29; source assertion 247
    ((a 1 3) ≥ 0) →
    -- core premise 30; source assertion 253
    ((a 1 5) ≥ 0) →
    -- core premise 31; source assertion 295
    ((a 1 19) ≥ 0) →
    -- core premise 32; source assertion 313
    ((a 1 25) ≥ 0) →
    -- core premise 33; source assertion 334
    (((a 1 0) + (a 1 1) + (a 1 2) + (a 1 3) + (a 1 4) + (a 1 5) + (a 1 6) + (a 1 7) + (a 1 8) + (a 1 9) + (a 1 10) + (a 1 11) + (a 1 12) + (a 1 13) + (a 1 14) + (a 1 15) + (a 1 16) + (a 1 17) + (a 1 18) + (a 1 19) + (a 1 20) + (a 1 21) + (a 1 22) + (a 1 23) + (a 1 24) + (a 1 25) + (a 1 26) + (a 1 27) + (a 1 28) + (a 1 29) + (a 1 30) + (a 1 31)) = 58564) →
    -- core premise 34; source assertion 341
    (((a 1 0) + (a 1 4) + (a 1 8) + (a 1 12) + (a 1 16) + (a 1 20) + (a 1 24) + (a 1 28)) ≥ 9762) →
    -- core premise 35; source assertion 361
    (((a 1 0) + (a 1 2) + (a 1 16) + (a 1 18)) ≥ 854) →
    -- core premise 36; source assertion 373
    (((a 1 0) + (a 1 4) + (a 1 8) + (a 1 12)) ≥ 902) →
    -- core premise 37; source assertion 377
    (((a 1 0) + (a 1 2) + (a 1 8) + (a 1 10)) ≥ 550) →
    -- core premise 38; source assertion 379
    (((a 1 0) + (a 1 1) + (a 1 8) + (a 1 9)) ≥ 396) →
    -- core premise 39; source assertion 385
    (((a 1 0) + (a 1 2) + (a 1 4) + (a 1 6)) ≥ 418) →
    -- core premise 40; source assertion 403
    (((2 * (a 1 0)) + ((-2) * (a 1 1)) + ((-1) * (a 1 2)) + (1 * (a 1 3)) + (2 * (a 1 4)) + ((-2) * (a 1 5)) + ((-1) * (a 1 6)) + (1 * (a 1 7)) + (2 * (a 1 8)) + ((-2) * (a 1 9)) + ((-1) * (a 1 10)) + (1 * (a 1 11)) + (2 * (a 1 12)) + ((-2) * (a 1 13)) + ((-1) * (a 1 14)) + (1 * (a 1 15)) + (2 * (a 1 16)) + ((-2) * (a 1 17)) + ((-1) * (a 1 18)) + (1 * (a 1 19)) + (2 * (a 1 20)) + ((-2) * (a 1 21)) + ((-1) * (a 1 22)) + (1 * (a 1 23)) + (2 * (a 1 24)) + ((-2) * (a 1 25)) + ((-1) * (a 1 26)) + (1 * (a 1 27)) + (2 * (a 1 28)) + ((-2) * (a 1 29)) + ((-1) * (a 1 30)) + (1 * (a 1 31))) ≥ 0) →
    -- core premise 41; source assertion 407
    (((4 * (a 1 0)) + ((-4) * (a 1 1)) + (4 * (a 1 2)) + ((-4) * (a 1 3)) + ((-1) * (a 1 4)) + (1 * (a 1 5)) + ((-1) * (a 1 6)) + (1 * (a 1 7)) + (4 * (a 1 8)) + ((-4) * (a 1 9)) + (4 * (a 1 10)) + ((-4) * (a 1 11)) + ((-1) * (a 1 12)) + (1 * (a 1 13)) + ((-1) * (a 1 14)) + (1 * (a 1 15)) + (4 * (a 1 16)) + ((-4) * (a 1 17)) + (4 * (a 1 18)) + ((-4) * (a 1 19)) + ((-1) * (a 1 20)) + (1 * (a 1 21)) + ((-1) * (a 1 22)) + (1 * (a 1 23)) + (4 * (a 1 24)) + ((-4) * (a 1 25)) + (4 * (a 1 26)) + ((-4) * (a 1 27)) + ((-1) * (a 1 28)) + (1 * (a 1 29)) + ((-1) * (a 1 30)) + (1 * (a 1 31))) ≥ 0) →
    -- core premise 42; source assertion 415
    (((6 * (a 1 0)) + ((-6) * (a 1 1)) + (6 * (a 1 2)) + ((-6) * (a 1 3)) + (6 * (a 1 4)) + ((-6) * (a 1 5)) + (6 * (a 1 6)) + ((-6) * (a 1 7)) + ((-1) * (a 1 8)) + (1 * (a 1 9)) + ((-1) * (a 1 10)) + (1 * (a 1 11)) + ((-1) * (a 1 12)) + (1 * (a 1 13)) + ((-1) * (a 1 14)) + (1 * (a 1 15)) + (6 * (a 1 16)) + ((-6) * (a 1 17)) + (6 * (a 1 18)) + ((-6) * (a 1 19)) + (6 * (a 1 20)) + ((-6) * (a 1 21)) + (6 * (a 1 22)) + ((-6) * (a 1 23)) + ((-1) * (a 1 24)) + (1 * (a 1 25)) + ((-1) * (a 1 26)) + (1 * (a 1 27)) + ((-1) * (a 1 28)) + (1 * (a 1 29)) + ((-1) * (a 1 30)) + (1 * (a 1 31))) ≥ 0) →
    -- core premise 43; source assertion 418
    ((z 1 10) ↔ (((12 * (a 1 0)) + (12 * (a 1 1)) + ((-6) * (a 1 2)) + ((-6) * (a 1 3)) + (12 * (a 1 4)) + (12 * (a 1 5)) + ((-6) * (a 1 6)) + ((-6) * (a 1 7)) + ((-2) * (a 1 8)) + ((-2) * (a 1 9)) + (1 * (a 1 10)) + (1 * (a 1 11)) + ((-2) * (a 1 12)) + ((-2) * (a 1 13)) + (1 * (a 1 14)) + (1 * (a 1 15)) + (12 * (a 1 16)) + (12 * (a 1 17)) + ((-6) * (a 1 18)) + ((-6) * (a 1 19)) + (12 * (a 1 20)) + (12 * (a 1 21)) + ((-6) * (a 1 22)) + ((-6) * (a 1 23)) + ((-2) * (a 1 24)) + ((-2) * (a 1 25)) + (1 * (a 1 26)) + (1 * (a 1 27)) + ((-2) * (a 1 28)) + ((-2) * (a 1 29)) + (1 * (a 1 30)) + (1 * (a 1 31))) = 0)) →
    -- core premise 44; source assertion 422
    ((z 1 12) ↔ (((24 * (a 1 0)) + (24 * (a 1 1)) + (24 * (a 1 2)) + (24 * (a 1 3)) + ((-6) * (a 1 4)) + ((-6) * (a 1 5)) + ((-6) * (a 1 6)) + ((-6) * (a 1 7)) + ((-4) * (a 1 8)) + ((-4) * (a 1 9)) + ((-4) * (a 1 10)) + ((-4) * (a 1 11)) + (1 * (a 1 12)) + (1 * (a 1 13)) + (1 * (a 1 14)) + (1 * (a 1 15)) + (24 * (a 1 16)) + (24 * (a 1 17)) + (24 * (a 1 18)) + (24 * (a 1 19)) + ((-6) * (a 1 20)) + ((-6) * (a 1 21)) + ((-6) * (a 1 22)) + ((-6) * (a 1 23)) + ((-4) * (a 1 24)) + ((-4) * (a 1 25)) + ((-4) * (a 1 26)) + ((-4) * (a 1 27)) + (1 * (a 1 28)) + (1 * (a 1 29)) + (1 * (a 1 30)) + (1 * (a 1 31))) = 0)) →
    -- core premise 45; source assertion 426
    ((z 1 14) ↔ (((48 * (a 1 0)) + (48 * (a 1 1)) + ((-24) * (a 1 2)) + ((-24) * (a 1 3)) + ((-12) * (a 1 4)) + ((-12) * (a 1 5)) + (6 * (a 1 6)) + (6 * (a 1 7)) + ((-8) * (a 1 8)) + ((-8) * (a 1 9)) + (4 * (a 1 10)) + (4 * (a 1 11)) + (2 * (a 1 12)) + (2 * (a 1 13)) + ((-1) * (a 1 14)) + ((-1) * (a 1 15)) + (48 * (a 1 16)) + (48 * (a 1 17)) + ((-24) * (a 1 18)) + ((-24) * (a 1 19)) + ((-12) * (a 1 20)) + ((-12) * (a 1 21)) + (6 * (a 1 22)) + (6 * (a 1 23)) + ((-8) * (a 1 24)) + ((-8) * (a 1 25)) + (4 * (a 1 26)) + (4 * (a 1 27)) + (2 * (a 1 28)) + (2 * (a 1 29)) + ((-1) * (a 1 30)) + ((-1) * (a 1 31))) = 0)) →
    -- core premise 46; source assertion 428
    ((z 1 15) ↔ (((48 * (a 1 0)) + ((-48) * (a 1 1)) + ((-24) * (a 1 2)) + (24 * (a 1 3)) + ((-12) * (a 1 4)) + (12 * (a 1 5)) + (6 * (a 1 6)) + ((-6) * (a 1 7)) + ((-8) * (a 1 8)) + (8 * (a 1 9)) + (4 * (a 1 10)) + ((-4) * (a 1 11)) + (2 * (a 1 12)) + ((-2) * (a 1 13)) + ((-1) * (a 1 14)) + (1 * (a 1 15)) + (48 * (a 1 16)) + ((-48) * (a 1 17)) + ((-24) * (a 1 18)) + (24 * (a 1 19)) + ((-12) * (a 1 20)) + (12 * (a 1 21)) + (6 * (a 1 22)) + ((-6) * (a 1 23)) + ((-8) * (a 1 24)) + (8 * (a 1 25)) + (4 * (a 1 26)) + ((-4) * (a 1 27)) + (2 * (a 1 28)) + ((-2) * (a 1 29)) + ((-1) * (a 1 30)) + (1 * (a 1 31))) = 0)) →
    -- core premise 47; source assertion 430
    ((z 1 16) ↔ (((10 * (a 1 0)) + (10 * (a 1 1)) + (10 * (a 1 2)) + (10 * (a 1 3)) + (10 * (a 1 4)) + (10 * (a 1 5)) + (10 * (a 1 6)) + (10 * (a 1 7)) + (10 * (a 1 8)) + (10 * (a 1 9)) + (10 * (a 1 10)) + (10 * (a 1 11)) + (10 * (a 1 12)) + (10 * (a 1 13)) + (10 * (a 1 14)) + (10 * (a 1 15)) + ((-1) * (a 1 16)) + ((-1) * (a 1 17)) + ((-1) * (a 1 18)) + ((-1) * (a 1 19)) + ((-1) * (a 1 20)) + ((-1) * (a 1 21)) + ((-1) * (a 1 22)) + ((-1) * (a 1 23)) + ((-1) * (a 1 24)) + ((-1) * (a 1 25)) + ((-1) * (a 1 26)) + ((-1) * (a 1 27)) + ((-1) * (a 1 28)) + ((-1) * (a 1 29)) + ((-1) * (a 1 30)) + ((-1) * (a 1 31))) = 0)) →
    -- core premise 48; source assertion 433
    (((20 * (a 1 0)) + (20 * (a 1 1)) + ((-10) * (a 1 2)) + ((-10) * (a 1 3)) + (20 * (a 1 4)) + (20 * (a 1 5)) + ((-10) * (a 1 6)) + ((-10) * (a 1 7)) + (20 * (a 1 8)) + (20 * (a 1 9)) + ((-10) * (a 1 10)) + ((-10) * (a 1 11)) + (20 * (a 1 12)) + (20 * (a 1 13)) + ((-10) * (a 1 14)) + ((-10) * (a 1 15)) + ((-2) * (a 1 16)) + ((-2) * (a 1 17)) + (1 * (a 1 18)) + (1 * (a 1 19)) + ((-2) * (a 1 20)) + ((-2) * (a 1 21)) + (1 * (a 1 22)) + (1 * (a 1 23)) + ((-2) * (a 1 24)) + ((-2) * (a 1 25)) + (1 * (a 1 26)) + (1 * (a 1 27)) + ((-2) * (a 1 28)) + ((-2) * (a 1 29)) + (1 * (a 1 30)) + (1 * (a 1 31))) ≥ 0) →
    -- core premise 49; source assertion 435
    (((20 * (a 1 0)) + ((-20) * (a 1 1)) + ((-10) * (a 1 2)) + (10 * (a 1 3)) + (20 * (a 1 4)) + ((-20) * (a 1 5)) + ((-10) * (a 1 6)) + (10 * (a 1 7)) + (20 * (a 1 8)) + ((-20) * (a 1 9)) + ((-10) * (a 1 10)) + (10 * (a 1 11)) + (20 * (a 1 12)) + ((-20) * (a 1 13)) + ((-10) * (a 1 14)) + (10 * (a 1 15)) + ((-2) * (a 1 16)) + (2 * (a 1 17)) + (1 * (a 1 18)) + ((-1) * (a 1 19)) + ((-2) * (a 1 20)) + (2 * (a 1 21)) + (1 * (a 1 22)) + ((-1) * (a 1 23)) + ((-2) * (a 1 24)) + (2 * (a 1 25)) + (1 * (a 1 26)) + ((-1) * (a 1 27)) + ((-2) * (a 1 28)) + (2 * (a 1 29)) + (1 * (a 1 30)) + ((-1) * (a 1 31))) ≥ 0) →
    -- core premise 50; source assertion 441
    (((80 * (a 1 0)) + (80 * (a 1 1)) + ((-40) * (a 1 2)) + ((-40) * (a 1 3)) + ((-20) * (a 1 4)) + ((-20) * (a 1 5)) + (10 * (a 1 6)) + (10 * (a 1 7)) + (80 * (a 1 8)) + (80 * (a 1 9)) + ((-40) * (a 1 10)) + ((-40) * (a 1 11)) + ((-20) * (a 1 12)) + ((-20) * (a 1 13)) + (10 * (a 1 14)) + (10 * (a 1 15)) + ((-8) * (a 1 16)) + ((-8) * (a 1 17)) + (4 * (a 1 18)) + (4 * (a 1 19)) + (2 * (a 1 20)) + (2 * (a 1 21)) + ((-1) * (a 1 22)) + ((-1) * (a 1 23)) + ((-8) * (a 1 24)) + ((-8) * (a 1 25)) + (4 * (a 1 26)) + (4 * (a 1 27)) + (2 * (a 1 28)) + (2 * (a 1 29)) + ((-1) * (a 1 30)) + ((-1) * (a 1 31))) ≥ 0) →
    -- core premise 51; source assertion 443
    (((80 * (a 1 0)) + ((-80) * (a 1 1)) + ((-40) * (a 1 2)) + (40 * (a 1 3)) + ((-20) * (a 1 4)) + (20 * (a 1 5)) + (10 * (a 1 6)) + ((-10) * (a 1 7)) + (80 * (a 1 8)) + ((-80) * (a 1 9)) + ((-40) * (a 1 10)) + (40 * (a 1 11)) + ((-20) * (a 1 12)) + (20 * (a 1 13)) + (10 * (a 1 14)) + ((-10) * (a 1 15)) + ((-8) * (a 1 16)) + (8 * (a 1 17)) + (4 * (a 1 18)) + ((-4) * (a 1 19)) + (2 * (a 1 20)) + ((-2) * (a 1 21)) + ((-1) * (a 1 22)) + (1 * (a 1 23)) + ((-8) * (a 1 24)) + (8 * (a 1 25)) + (4 * (a 1 26)) + ((-4) * (a 1 27)) + (2 * (a 1 28)) + ((-2) * (a 1 29)) + ((-1) * (a 1 30)) + (1 * (a 1 31))) ≥ 0) →
    -- core premise 52; source assertion 445
    (((60 * (a 1 0)) + (60 * (a 1 1)) + (60 * (a 1 2)) + (60 * (a 1 3)) + (60 * (a 1 4)) + (60 * (a 1 5)) + (60 * (a 1 6)) + (60 * (a 1 7)) + ((-10) * (a 1 8)) + ((-10) * (a 1 9)) + ((-10) * (a 1 10)) + ((-10) * (a 1 11)) + ((-10) * (a 1 12)) + ((-10) * (a 1 13)) + ((-10) * (a 1 14)) + ((-10) * (a 1 15)) + ((-6) * (a 1 16)) + ((-6) * (a 1 17)) + ((-6) * (a 1 18)) + ((-6) * (a 1 19)) + ((-6) * (a 1 20)) + ((-6) * (a 1 21)) + ((-6) * (a 1 22)) + ((-6) * (a 1 23)) + (1 * (a 1 24)) + (1 * (a 1 25)) + (1 * (a 1 26)) + (1 * (a 1 27)) + (1 * (a 1 28)) + (1 * (a 1 29)) + (1 * (a 1 30)) + (1 * (a 1 31))) ≥ 0) →
    -- core premise 53; source assertion 447
    (((60 * (a 1 0)) + ((-60) * (a 1 1)) + (60 * (a 1 2)) + ((-60) * (a 1 3)) + (60 * (a 1 4)) + ((-60) * (a 1 5)) + (60 * (a 1 6)) + ((-60) * (a 1 7)) + ((-10) * (a 1 8)) + (10 * (a 1 9)) + ((-10) * (a 1 10)) + (10 * (a 1 11)) + ((-10) * (a 1 12)) + (10 * (a 1 13)) + ((-10) * (a 1 14)) + (10 * (a 1 15)) + ((-6) * (a 1 16)) + (6 * (a 1 17)) + ((-6) * (a 1 18)) + (6 * (a 1 19)) + ((-6) * (a 1 20)) + (6 * (a 1 21)) + ((-6) * (a 1 22)) + (6 * (a 1 23)) + (1 * (a 1 24)) + ((-1) * (a 1 25)) + (1 * (a 1 26)) + ((-1) * (a 1 27)) + (1 * (a 1 28)) + ((-1) * (a 1 29)) + (1 * (a 1 30)) + ((-1) * (a 1 31))) ≥ 0) →
    -- core premise 54; source assertion 449
    (((120 * (a 1 0)) + (120 * (a 1 1)) + ((-60) * (a 1 2)) + ((-60) * (a 1 3)) + (120 * (a 1 4)) + (120 * (a 1 5)) + ((-60) * (a 1 6)) + ((-60) * (a 1 7)) + ((-20) * (a 1 8)) + ((-20) * (a 1 9)) + (10 * (a 1 10)) + (10 * (a 1 11)) + ((-20) * (a 1 12)) + ((-20) * (a 1 13)) + (10 * (a 1 14)) + (10 * (a 1 15)) + ((-12) * (a 1 16)) + ((-12) * (a 1 17)) + (6 * (a 1 18)) + (6 * (a 1 19)) + ((-12) * (a 1 20)) + ((-12) * (a 1 21)) + (6 * (a 1 22)) + (6 * (a 1 23)) + (2 * (a 1 24)) + (2 * (a 1 25)) + ((-1) * (a 1 26)) + ((-1) * (a 1 27)) + (2 * (a 1 28)) + (2 * (a 1 29)) + ((-1) * (a 1 30)) + ((-1) * (a 1 31))) ≥ 0) →
    -- core premise 55; source assertion 451
    (((120 * (a 1 0)) + ((-120) * (a 1 1)) + ((-60) * (a 1 2)) + (60 * (a 1 3)) + (120 * (a 1 4)) + ((-120) * (a 1 5)) + ((-60) * (a 1 6)) + (60 * (a 1 7)) + ((-20) * (a 1 8)) + (20 * (a 1 9)) + (10 * (a 1 10)) + ((-10) * (a 1 11)) + ((-20) * (a 1 12)) + (20 * (a 1 13)) + (10 * (a 1 14)) + ((-10) * (a 1 15)) + ((-12) * (a 1 16)) + (12 * (a 1 17)) + (6 * (a 1 18)) + ((-6) * (a 1 19)) + ((-12) * (a 1 20)) + (12 * (a 1 21)) + (6 * (a 1 22)) + ((-6) * (a 1 23)) + (2 * (a 1 24)) + ((-2) * (a 1 25)) + ((-1) * (a 1 26)) + (1 * (a 1 27)) + (2 * (a 1 28)) + ((-2) * (a 1 29)) + ((-1) * (a 1 30)) + (1 * (a 1 31))) ≥ 0) →
    -- core premise 56; source assertion 462
    ((a 1 2) = 0) →
    -- core premise 57; source assertion 464
    ((a 1 4) = 0) →
    -- core premise 58; source assertion 466
    ((a 1 8) = 0) →
    -- core premise 59; source assertion 491
    (((a 1 6) > 0) → (z 0 6)) →
    -- core premise 60; source assertion 497
    (((a 1 9) > 0) → (z 0 9)) →
    -- core premise 61; source assertion 498
    (((a 0 10) > 0) → (z 1 10)) →
    -- core premise 62; source assertion 499
    (((a 1 10) > 0) → (z 0 10)) →
    -- core premise 63; source assertion 502
    (((a 0 12) > 0) → (z 1 12)) →
    -- core premise 64; source assertion 503
    (((a 1 12) > 0) → (z 0 12)) →
    -- core premise 65; source assertion 506
    (((a 0 14) > 0) → (z 1 14)) →
    -- core premise 66; source assertion 508
    (((a 0 15) > 0) → (z 1 15)) →
    -- core premise 67; source assertion 510
    (((a 0 16) > 0) → (z 1 16)) →
    -- core premise 68; source assertion 515
    (((a 1 18) > 0) → (z 0 18)) →
    -- core premise 69; source assertion 527
    (((a 1 24) > 0) → (z 0 24)) →
    False

theorem baseUnsatAt_242_of_k242CompactShardedRawCertificate
    (hraw : K242CompactShardedRawCertificate) : BaseUnsatAt 242 := by
  intro a z hconstraints
  unfold K242CompactShardedRawCertificate at hraw
  apply hraw
    (fun s m => a s (axisSupportOfMask m.val))
    (fun s m => z s (axisSupportOfMask m.val))
  · exact k242CorePremise0 a z hconstraints
  · exact k242CorePremise1 a z hconstraints
  · exact k242CorePremise2 a z hconstraints
  · exact k242CorePremise3 a z hconstraints
  · exact k242CorePremise4 a z hconstraints
  · exact k242CorePremise5 a z hconstraints
  · exact k242CorePremise6 a z hconstraints
  · exact k242CorePremise7 a z hconstraints
  · exact k242CorePremise8 a z hconstraints
  · exact k242CorePremise9 a z hconstraints
  · exact k242CorePremise10 a z hconstraints
  · exact k242CorePremise11 a z hconstraints
  · exact k242CorePremise12 a z hconstraints
  · exact k242CorePremise13 a z hconstraints
  · exact k242CorePremise14 a z hconstraints
  · exact k242CorePremise15 a z hconstraints
  · exact k242CorePremise16 a z hconstraints
  · exact k242CorePremise17 a z hconstraints
  · exact k242CorePremise18 a z hconstraints
  · exact k242CorePremise19 a z hconstraints
  · exact k242CorePremise20 a z hconstraints
  · exact k242CorePremise21 a z hconstraints
  · exact k242CorePremise22 a z hconstraints
  · exact k242CorePremise23 a z hconstraints
  · exact k242CorePremise24 a z hconstraints
  · exact k242CorePremise25 a z hconstraints
  · exact k242CorePremise26 a z hconstraints
  · exact k242CorePremise27 a z hconstraints
  · exact k242CorePremise28 a z hconstraints
  · exact k242CorePremise29 a z hconstraints
  · exact k242CorePremise30 a z hconstraints
  · exact k242CorePremise31 a z hconstraints
  · exact k242CorePremise32 a z hconstraints
  · exact k242CorePremise33 a z hconstraints
  · exact k242CorePremise34 a z hconstraints
  · exact k242CorePremise35 a z hconstraints
  · exact k242CorePremise36 a z hconstraints
  · exact k242CorePremise37 a z hconstraints
  · exact k242CorePremise38 a z hconstraints
  · exact k242CorePremise39 a z hconstraints
  · exact k242CorePremise40 a z hconstraints
  · exact k242CorePremise41 a z hconstraints
  · exact k242CorePremise42 a z hconstraints
  · exact k242CorePremise43 a z hconstraints
  · exact k242CorePremise44 a z hconstraints
  · exact k242CorePremise45 a z hconstraints
  · exact k242CorePremise46 a z hconstraints
  · exact k242CorePremise47 a z hconstraints
  · exact k242CorePremise48 a z hconstraints
  · exact k242CorePremise49 a z hconstraints
  · exact k242CorePremise50 a z hconstraints
  · exact k242CorePremise51 a z hconstraints
  · exact k242CorePremise52 a z hconstraints
  · exact k242CorePremise53 a z hconstraints
  · exact k242CorePremise54 a z hconstraints
  · exact k242CorePremise55 a z hconstraints
  · exact k242CorePremise56 a z hconstraints
  · exact k242CorePremise57 a z hconstraints
  · exact k242CorePremise58 a z hconstraints
  · exact k242CorePremise59 a z hconstraints
  · exact k242CorePremise60 a z hconstraints
  · exact k242CorePremise61 a z hconstraints
  · exact k242CorePremise62 a z hconstraints
  · exact k242CorePremise63 a z hconstraints
  · exact k242CorePremise64 a z hconstraints
  · exact k242CorePremise65 a z hconstraints
  · exact k242CorePremise66 a z hconstraints
  · exact k242CorePremise67 a z hconstraints
  · exact k242CorePremise68 a z hconstraints
  · exact k242CorePremise69 a z hconstraints

end Fuglede
