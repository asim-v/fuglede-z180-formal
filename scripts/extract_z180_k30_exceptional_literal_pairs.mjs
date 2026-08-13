#!/usr/bin/env node
"use strict";

import assert from "node:assert/strict";
import crypto from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const N = 36;
const PHI_DEGREE = 12;
const DIVISORS = [3, 4, 6];
const UNITS = [1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35];
const ORBIT_REPRESENTATIVES = [
  [0, 1, 12, 18, 24, 30],
  [0, 10, 12, 18, 24, 30],
  [0, 10, 12, 22, 24, 34],
  [0, 12, 15, 18, 24, 30],
  [0, 12, 15, 18, 30, 33],
  [0, 12, 16, 18, 24, 30],
  [0, 12, 18, 21, 24, 30],
  [0, 6, 12, 18, 24, 30]
];

function gcd(a, b) {
  a = Math.abs(a);
  b = Math.abs(b);
  while (b !== 0) [a, b] = [b, a % b];
  return a;
}

function choose(values, size, callback, start = 0, picked = []) {
  if (picked.length === size) {
    callback(picked.slice());
    return;
  }
  for (let i = start; i <= values.length - (size - picked.length); i += 1) {
    picked.push(values[i]);
    choose(values, size, callback, i + 1, picked);
    picked.pop();
  }
}

function reducedPower(exponent) {
  const coefficients = Array(N).fill(0);
  coefficients[((exponent % N) + N) % N] = 1;
  for (let degree = N - 1; degree >= PHI_DEGREE; degree -= 1) {
    const coefficient = coefficients[degree];
    if (coefficient !== 0) {
      coefficients[degree] = 0;
      coefficients[degree - 6] += coefficient;
      coefficients[degree - 12] -= coefficient;
    }
  }
  return coefficients.slice(0, PHI_DEGREE);
}

const POWER = Array.from({ length: N }, (_, exponent) => reducedPower(exponent));

function add(target, source) {
  for (let i = 0; i < PHI_DEGREE; i += 1) target[i] += source[i];
}

function differenceGcd(set) {
  let result = N;
  for (const value of set) result = gcd(result, value - set[0]);
  return result;
}

function classCount(set, modulus) {
  return new Set(set.map((value) => value % modulus)).size;
}

function energyTable(V) {
  return Array.from({ length: N }, (_, difference) => {
    const result = Array(PHI_DEGREE).fill(0);
    for (const v of V) {
      for (const w of V) {
        add(result, POWER[((difference * (v - w)) % N + N) % N]);
      }
    }
    return result;
  });
}

function gramTraceSquare(U, energies) {
  const result = Array(PHI_DEGREE).fill(0);
  for (const u of U) {
    for (const w of U) add(result, energies[((u - w) % N + N) % N]);
  }
  return result;
}

function isScalar(vector, scalar) {
  return vector[0] === scalar && vector.slice(1).every((value) => value === 0);
}

function rankAtMostTwo(U, V) {
  return classCount(U, N / differenceGcd(V)) <= 2 ||
    classCount(V, N / differenceGcd(U)) <= 2;
}

function sameSet(left, right) {
  return left.length === right.length && left.every((value) => right.includes(value));
}

function affineWitness(set) {
  for (let representative = 0; representative < ORBIT_REPRESENTATIVES.length;
      representative += 1) {
    const source = ORBIT_REPRESENTATIVES[representative];
    for (const unit of UNITS) {
      for (let translation = 0; translation < N; translation += 1) {
        const transformed = source.map((value) =>
          (unit * value + translation) % N);
        if (sameSet(transformed, set)) return { representative, unit, translation };
      }
    }
  }
  return null;
}

function pairKey(U, V) {
  return `${U.join(",")}|${V.join(",")}`;
}

function extract() {
  const occurrences = [];
  const unique = new Map();
  const byDivisor = [];
  let enumeratedTotal = 0;

  for (const divisor of DIVISORS) {
    const base = Array.from({ length: N / divisor }, (_, index) => divisor * index);
    const vChoices = [];
    choose(base, 6, (V) => vChoices.push(V));
    const modulus = N / divisor;
    const classes = Array.from({ length: modulus }, (_, residue) =>
      Array.from({ length: divisor }, (_, index) => residue + modulus * index));
    const classPairs = [];
    choose(Array.from({ length: modulus }, (_, index) => index), 2,
      (pair) => classPairs.push(pair));

    let enumerated = 0;
    let accepted = 0;
    for (let vIndex = 0; vIndex < vChoices.length; vIndex += 1) {
      const V = vChoices[vIndex];
      const energies = energyTable(V);
      for (let pairIndex = 0; pairIndex < classPairs.length; pairIndex += 1) {
        const [first, second] = classPairs[pairIndex];
        choose([...classes[first], ...classes[second]], 6, (U) => {
          enumerated += 1;
          if (!rankAtMostTwo(U, V) || !isScalar(gramTraceSquare(U, energies), 936)) return;
          accepted += 1;
          const key = pairKey(U, V);
          const record = { divisor, vIndex, pairIndex, U, V };
          occurrences.push(record);
          if (!unique.has(key)) unique.set(key, record);
        });
      }
    }
    enumeratedTotal += enumerated;
    byDivisor.push({ divisor, enumerated, accepted });
  }

  assert.equal(enumeratedTotal, 159516);
  assert.equal(occurrences.length, 1584);
  assert.deepStrictEqual(byDivisor.map(({ accepted }) => accepted), [504, 0, 1080]);

  const pairs = [...unique.values()].map((record) => {
    const uWitness = affineWitness(record.U);
    const vWitness = affineWitness(record.V);
    assert.ok(uWitness, `missing orbit witness for U=${record.U}`);
    assert.ok(vWitness, `missing orbit witness for V=${record.V}`);
    return { ...record, uWitness, vWitness };
  });

  return {
    schema: "z180-k30-exceptional-literal-pairs/v1",
    enumeratedTotal,
    acceptedOccurrences: occurrences.length,
    uniqueAcceptedPairs: pairs.length,
    byDivisor,
    pairs
  };
}

function leanList(values) {
  return `[${values.join(", ")}]`;
}

function leanPair(record) {
  return `(${leanList(record.U)}, ${leanList(record.V)})`;
}

function renderLeanShard(records, index) {
  const suffix = String(index).padStart(2, "0");
  const pairs = records.map((record) => `    ${leanPair(record)}`).join(",\n");
  return `import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard ${suffix}; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard${suffix} :
    List (RawSet × RawSet) :=
  [
${pairs}
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard${suffix} :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard${suffix}.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
`;
}

function renderLeanAggregate(payload, shardSize, shardCount) {
  const imports = [];
  const records = [];
  for (let index = 0; index < shardCount; index += 1) {
    const suffix = String(index).padStart(2, "0");
    const shardRecords = payload.pairs.slice(index * shardSize, (index + 1) * shardSize);
    const divisors = [...new Set(shardRecords.map((record) => record.divisor))];
    assert.equal(divisors.length, 1, `mixed divisors in Lean shard ${suffix}`);
    const divisor = divisors[0];
    const supported = divisor === 3 ? "Or.inl rfl" :
      divisor === 4 ? "Or.inr (Or.inl rfl)" : "Or.inr (Or.inr rfl)";
    imports.push(`import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsV85Shard${suffix}`);
    records.push(`    { divisor := ${divisor}
      supported_divisor := ${supported}
      pairs := z180K30ExceptionalLiteralAcceptedPairsV85Shard${suffix}
      covered := z180_k30_exceptional_literal_accepted_pairs_v85_shard${suffix} }`);
  }
  return `${imports.join("\n")}

/-! Semantic aggregate for the 1584 literal accepted projective pairs. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairShardsV85 :
    List CertifiedLiteralAcceptedPairShardV85 :=
  [
${records.join(",\n")}
  ]

def z180K30ExceptionalLiteralAcceptedPairsV85 :
    List (RawSet × RawSet) :=
  z180K30ExceptionalLiteralAcceptedPairShardsV85.flatMap
    CertifiedLiteralAcceptedPairShardV85.pairs

theorem z180_k30_exceptional_literal_accepted_pair_covered_v85
    (U V : RawSet)
    (hmem : (U, V) ∈ z180K30ExceptionalLiteralAcceptedPairsV85) :
    exceptionalPairB U V = true ∧
      orbitCoveredB U = true ∧ orbitCoveredB V = true := by
  rw [z180K30ExceptionalLiteralAcceptedPairsV85] at hmem
  rcases List.mem_flatMap.mp hmem with ⟨shard, _hshard, hpair⟩
  have hcovered := (List.all_eq_true.mp shard.covered) (U, V) hpair
  simpa only [literalExceptionalPairCoveredB_v85,
    Bool.and_eq_true] using hcovered

#print axioms z180_k30_exceptional_literal_accepted_pair_covered_v85

end Fuglede.Z180K30ExceptionalRawV2
`;
}

function emitLeanShards(payload, directory, shardSize) {
  fs.mkdirSync(directory, { recursive: true });
  const shardCount = Math.ceil(payload.pairs.length / shardSize);
  for (let index = 0; index < shardCount; index += 1) {
    const records = payload.pairs.slice(index * shardSize, (index + 1) * shardSize);
    const suffix = String(index).padStart(2, "0");
    const file = path.join(directory,
      `Z180K30ExceptionalLiteralAcceptedPairsV85Shard${suffix}.lean`);
    fs.writeFileSync(file, renderLeanShard(records, index));
  }
  fs.writeFileSync(path.join(directory,
    "Z180K30ExceptionalLiteralAcceptedPairsAggregateV85.lean"),
    renderLeanAggregate(payload, shardSize, shardCount));
  return shardCount;
}

function sha256File(file) {
  return crypto.createHash("sha256").update(fs.readFileSync(file))
    .digest("hex").toUpperCase();
}

function emitLeanHashManifest(directory, shardCount, destination) {
  const files = [
    ...Array.from({ length: shardCount }, (_, index) => path.join(directory,
      `Z180K30ExceptionalLiteralAcceptedPairsV85Shard${String(index).padStart(2, "0")}.lean`)),
    path.join(directory, "Z180K30ExceptionalLiteralAcceptedPairsAggregateV85.lean")
  ];
  const lines = files.map((file) =>
    `${sha256File(file)}  ${path.basename(file)}`);
  fs.writeFileSync(destination, `${lines.join("\n")}\n`);
}

function renderLeanWitness(record) {
  return `    ⟨${leanList(record.U)}, ${leanList(record.V)},
      ${record.uWitness.representative}, ${record.uWitness.unit},
      ${record.uWitness.translation}, ${record.vWitness.representative},
      ${record.vWitness.unit}, ${record.vWitness.translation}⟩`;
}

function renderLeanWitnessShard(records, index) {
  const suffix = String(index).padStart(2, "0");
  return `import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard ${suffix}; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard${suffix} :
    List LiteralExceptionalPairWitnessV87 :=
  [
${records.map(renderLeanWitness).join(",\n")}
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard${suffix} :
    z180K30ExceptionalLiteralWitnessesV87Shard${suffix}.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
`;
}

function renderLeanWitnessAggregate(payload, shardSize, shardCount) {
  const imports = [];
  const records = [];
  for (let index = 0; index < shardCount; index += 1) {
    const suffix = String(index).padStart(2, "0");
    const shardRecords = payload.pairs.slice(index * shardSize, (index + 1) * shardSize);
    const divisors = [...new Set(shardRecords.map((record) => record.divisor))];
    assert.equal(divisors.length, 1, `mixed divisors in witness shard ${suffix}`);
    const divisor = divisors[0];
    const supported = divisor === 3 ? "Or.inl rfl" :
      divisor === 4 ? "Or.inr (Or.inl rfl)" : "Or.inr (Or.inr rfl)";
    imports.push(`import Fuglede.Z180K30ExceptionalLiteralWitnessV87Shard${suffix}`);
    records.push(`    { divisor := ${divisor}
      supported_divisor := ${supported}
      witnesses := z180K30ExceptionalLiteralWitnessesV87Shard${suffix}
      verified := z180_k30_exceptional_literal_witnesses_v87_shard${suffix} }`);
  }
  return `${imports.join("\n")}

/-! Semantic aggregate for all 1584 explicit affine witnesses. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessShardsV87 :
    List CertifiedLiteralExceptionalWitnessShardV87 :=
  [
${records.join(",\n")}
  ]

def z180K30ExceptionalLiteralWitnessesV87 :
    List LiteralExceptionalPairWitnessV87 :=
  z180K30ExceptionalLiteralWitnessShardsV87.flatMap
    CertifiedLiteralExceptionalWitnessShardV87.witnesses

theorem z180_k30_exceptional_literal_witness_semantics_v87
    (w : LiteralExceptionalPairWitnessV87)
    (hmem : w ∈ z180K30ExceptionalLiteralWitnessesV87) :
    exceptionalPairB w.U w.V = true ∧
      orbitCoveredB w.U = true ∧ orbitCoveredB w.V = true := by
  rw [z180K30ExceptionalLiteralWitnessesV87] at hmem
  rcases List.mem_flatMap.mp hmem with ⟨shard, _hshard, hw⟩
  exact literalExceptionalPairWitnessB_v87_semantics w
    ((List.all_eq_true.mp shard.verified) w hw)

#print axioms z180_k30_exceptional_literal_witness_semantics_v87

end Fuglede.Z180K30ExceptionalRawV2
`;
}

function emitLeanWitnessShards(payload, directory, shardSize) {
  fs.mkdirSync(directory, { recursive: true });
  const shardCount = Math.ceil(payload.pairs.length / shardSize);
  for (let index = 0; index < shardCount; index += 1) {
    const records = payload.pairs.slice(index * shardSize, (index + 1) * shardSize);
    const suffix = String(index).padStart(2, "0");
    fs.writeFileSync(path.join(directory,
      `Z180K30ExceptionalLiteralWitnessV87Shard${suffix}.lean`),
    renderLeanWitnessShard(records, index));
  }
  fs.writeFileSync(path.join(directory,
    "Z180K30ExceptionalLiteralWitnessAggregateV87.lean"),
  renderLeanWitnessAggregate(payload, shardSize, shardCount));
  return shardCount;
}

function emitLeanWitnessHashManifest(directory, shardCount, destination) {
  const files = [
    ...Array.from({ length: shardCount }, (_, index) => path.join(directory,
      `Z180K30ExceptionalLiteralWitnessV87Shard${String(index).padStart(2, "0")}.lean`)),
    path.join(directory, "Z180K30ExceptionalLiteralWitnessAggregateV87.lean")
  ];
  const lines = files.map((file) =>
    `${sha256File(file)}  ${path.basename(file)}`);
  fs.writeFileSync(destination, `${lines.join("\n")}\n`);
}

const extracted = extract();
const payload = `${JSON.stringify(extracted, null, 2)}\n`;
const hash = crypto.createHash("sha256").update(payload).digest("hex").toUpperCase();
const scriptDirectory = path.dirname(fileURLToPath(import.meta.url));
const outputFlag = process.argv.indexOf("--output");
if (outputFlag >= 0) {
  assert.ok(process.argv[outputFlag + 1], "--output requires a path");
  fs.writeFileSync(path.resolve(process.argv[outputFlag + 1]), payload);
}
const leanDirectoryFlag = process.argv.indexOf("--lean-directory");
let leanShardCount = 0;
if (leanDirectoryFlag >= 0) {
  assert.ok(process.argv[leanDirectoryFlag + 1], "--lean-directory requires a path");
  const shardSizeFlag = process.argv.indexOf("--lean-shard-size");
  const shardSize = shardSizeFlag >= 0 ? Number(process.argv[shardSizeFlag + 1]) : 8;
  assert.ok(Number.isSafeInteger(shardSize) && shardSize > 0,
    "--lean-shard-size must be a positive integer");
  leanShardCount = emitLeanShards(extracted,
    path.resolve(process.argv[leanDirectoryFlag + 1]), shardSize);
  const manifestFlag = process.argv.indexOf("--lean-hash-manifest");
  if (manifestFlag >= 0) {
    assert.ok(process.argv[manifestFlag + 1],
      "--lean-hash-manifest requires a path");
    emitLeanHashManifest(path.resolve(process.argv[leanDirectoryFlag + 1]),
      leanShardCount, path.resolve(process.argv[manifestFlag + 1]));
  }
}
const leanWitnessDirectoryFlag = process.argv.indexOf("--lean-witness-directory");
let leanWitnessShardCount = 0;
if (leanWitnessDirectoryFlag >= 0) {
  assert.ok(process.argv[leanWitnessDirectoryFlag + 1],
    "--lean-witness-directory requires a path");
  const shardSizeFlag = process.argv.indexOf("--lean-witness-shard-size");
  const shardSize = shardSizeFlag >= 0 ? Number(process.argv[shardSizeFlag + 1]) : 8;
  assert.ok(Number.isSafeInteger(shardSize) && shardSize > 0,
    "--lean-witness-shard-size must be a positive integer");
  const directory = path.resolve(process.argv[leanWitnessDirectoryFlag + 1]);
  leanWitnessShardCount = emitLeanWitnessShards(extracted, directory, shardSize);
  const manifestFlag = process.argv.indexOf("--lean-witness-hash-manifest");
  if (manifestFlag >= 0) {
    assert.ok(process.argv[manifestFlag + 1],
      "--lean-witness-hash-manifest requires a path");
    emitLeanWitnessHashManifest(directory, leanWitnessShardCount,
      path.resolve(process.argv[manifestFlag + 1]));
  }
}
process.stdout.write(JSON.stringify({ sha256: hash, leanShardCount,
  leanWitnessShardCount, ...JSON.parse(payload) }, null, 2));
