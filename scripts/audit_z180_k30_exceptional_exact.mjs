#!/usr/bin/env node
"use strict";

import assert from "node:assert/strict";
import crypto from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const N = 36;
const PHI_DEGREE = 12;
const UNITS = [1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35];
const EXPECTED_REPS = [
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

function binomial(n, k) {
  let result = 1;
  for (let i = 1; i <= k; i += 1) result = (result * (n - k + i)) / i;
  assert.ok(Number.isSafeInteger(result));
  return result;
}

// Exact basis 1,z,...,z^11 in Z[z]/(Phi_36), Phi_36=z^12-z^6+1.
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

function add(target, source, multiplier = 1) {
  for (let i = 0; i < PHI_DEGREE; i += 1) {
    target[i] += multiplier * source[i];
    assert.ok(Number.isSafeInteger(target[i]));
  }
}

function isScalar(vector, scalar) {
  return vector[0] === scalar && vector.slice(1).every((value) => value === 0);
}

function differenceGcd(set) {
  let result = N;
  for (const value of set) result = gcd(result, value - set[0]);
  return result;
}

function classCount(set, modulus) {
  return new Set(set.map((value) => ((value % modulus) + modulus) % modulus)).size;
}

function rankAtMostTwo(U, V) {
  return (
    classCount(U, N / differenceGcd(V)) <= 2 ||
    classCount(V, N / differenceGcd(U)) <= 2
  );
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

function gram(U, V) {
  const result = Array(6 * 6 * PHI_DEGREE).fill(0);
  for (let row = 0; row < 6; row += 1) {
    for (let column = 0; column < 6; column += 1) {
      const offset = (row * 6 + column) * PHI_DEGREE;
      const difference = V[column] - V[row];
      for (const u of U) {
        const power = POWER[((u * difference) % N + N) % N];
        for (let coefficient = 0; coefficient < PHI_DEGREE; coefficient += 1) {
          result[offset + coefficient] += power[coefficient];
        }
      }
    }
  }
  return result;
}

function compareSets(left, right) {
  const a = left.join(",");
  const b = right.join(",");
  return a < b ? -1 : a > b ? 1 : 0;
}

function affineRepresentative(set) {
  let bestKey = null;
  let bestSet = null;
  for (const unit of UNITS) {
    for (let translation = 0; translation < N; translation += 1) {
      const transformed = set
        .map((value) => (unit * value + translation) % N)
        .sort((a, b) => a - b);
      const key = transformed.join(",");
      if (bestKey === null || key < bestKey) {
        bestKey = key;
        bestSet = transformed;
      }
    }
  }
  return [bestKey, bestSet];
}

function projectiveReduction() {
  const orbitMap = new Map();
  const byDivisor = [];

  for (const divisor of [3, 4, 6]) {
    const base = Array.from({ length: N / divisor }, (_, index) => divisor * index);
    const VChoices = [];
    choose(base, 6, (V) => VChoices.push(V));

    const modulus = N / divisor;
    const classes = Array.from({ length: modulus }, (_, residue) =>
      Array.from({ length: divisor }, (_, index) => residue + modulus * index)
    );
    const classPairs = [];
    choose(Array.from({ length: modulus }, (_, index) => index), 2, (pair) =>
      classPairs.push(pair)
    );

    let enumerated = 0;
    let accepted = 0;

    for (const V of VChoices) {
      const energies = energyTable(V);
      for (const [first, second] of classPairs) {
        choose([...classes[first], ...classes[second]], 6, (U) => {
          enumerated += 1;
          if (isScalar(gramTraceSquare(U, energies), 936)) {
            accepted += 1;
            for (const set of [U, V]) {
              const [key, representative] = affineRepresentative(set);
              orbitMap.set(key, representative);
            }
          }
        });
      }
    }

    byDivisor.push({
      divisor,
      vChoices: VChoices.length,
      classPairs: classPairs.length,
      uChoicesPerPair: binomial(2 * divisor, 6),
      enumerated,
      accepted
    });
  }

  return {
    byDivisor,
    representatives: [...orbitMap.values()].sort(compareSets)
  };
}

function exceptionalUSets(V) {
  const candidates = new Map();
  const addCandidate = (set) => {
    const sorted = set.slice().sort((a, b) => a - b);
    candidates.set(sorted.join(","), sorted);
  };

  const gcdV = differenceGcd(V);
  if (gcdV >= 3) {
    const modulus = N / gcdV;
    const classes = Array.from({ length: modulus }, (_, residue) =>
      Array.from({ length: gcdV }, (_, index) => residue + modulus * index)
    );
    for (let first = 0; first < modulus; first += 1) {
      for (let second = first + 1; second < modulus; second += 1) {
        choose([...classes[first], ...classes[second]], 6, addCandidate);
      }
    }
  }

  for (const divisor of [3, 4, 6]) {
    const modulus = N / divisor;
    if (classCount(V, modulus) <= 2) {
      for (let residue = 0; residue < divisor; residue += 1) {
        choose(
          Array.from({ length: N / divisor }, (_, index) => residue + divisor * index),
          6,
          addCandidate
        );
      }
    }
  }

  const energies = energyTable(V);
  const accepted = [...candidates.values()].filter(
    (U) =>
      rankAtMostTwo(U, V) &&
      isScalar(gramTraceSquare(U, energies), 936)
  );
  return accepted.sort(compareSets);
}

function gramStarAudit(entries) {
  const grams = entries.map((entry) => entry.gram);
  const UChoices = entries.map((entry) => entry.U);
  const target = Array(6 * 6 * PHI_DEGREE).fill(0);
  for (let diagonal = 0; diagonal < 6; diagonal += 1) {
    target[(diagonal * 6 + diagonal) * PHI_DEGREE] = 30;
  }

  const key = (vector) => vector.join(",");
  const pairSums = new Map();
  let pairQueries = 0;

  for (let first = 0; first < grams.length; first += 1) {
    for (let second = first; second < grams.length; second += 1) {
      pairQueries += 1;
      const sum = grams[first].map((value, index) => value + grams[second][index]);
      if (!pairSums.has(key(sum))) pairSums.set(key(sum), [first, second]);
    }
  }

  let tripleQueries = 0;
  let witness = null;

  search: for (let first = 0; first < grams.length; first += 1) {
    for (let second = first; second < grams.length; second += 1) {
      for (let third = second; third < grams.length; third += 1) {
        tripleQueries += 1;
        const needed = target.map(
          (value, index) =>
            value - grams[first][index] - grams[second][index] - grams[third][index]
        );
        const pair = pairSums.get(key(needed));
        if (pair !== undefined) {
          witness = [...pair, first, second, third]
            .sort((a, b) => a - b)
            .map((index) => UChoices[index]);
          break search;
        }
      }
    }
  }

  return {
    pairQueries,
    uniquePairSums: pairSums.size,
    tripleQueries,
    witness
  };
}

function buildCertificate() {
  const reduction = projectiveReduction();
  assert.deepStrictEqual(reduction.representatives, EXPECTED_REPS);

  const gramStarAuditResult = reduction.representatives.map((V) => {
    const UChoices = exceptionalUSets(V);
    const gramMap = new Map();
    for (const U of UChoices) {
      const matrix = gram(U, V);
      if (!gramMap.has(matrix.join(","))) {
        gramMap.set(matrix.join(","), { U, gram: matrix });
      }
    }
    return {
      V,
      exceptionalUCount: UChoices.length,
      uniqueGramCount: gramMap.size,
      ...gramStarAudit([...gramMap.values()])
    };
  });

  const enumeratedCandidatePairs = reduction.byDivisor.reduce(
    (sum, entry) => sum + entry.enumerated,
    0
  );
  const acceptedExceptionalPairs = reduction.byDivisor.reduce(
    (sum, entry) => sum + entry.accepted,
    0
  );
  const surviving = gramStarAuditResult.filter((entry) => entry.witness !== null);

  assert.equal(enumeratedCandidatePairs, 159516);
  assert.equal(acceptedExceptionalPairs, 1584);
  assert.equal(reduction.representatives.length, 8);
  assert.equal(surviving.length, 1);
  assert.deepStrictEqual(surviving[0].V, [0, 6, 12, 18, 24, 30]);

  return {
    schema: "z180-k30-exceptional-exact/v1",
    arithmetic: {
      conductor: 36,
      cyclotomicPolynomial: "x^12-x^6+1",
      basis: "1,x,...,x^11",
      floatingPointUsed: false
    },
    projectiveReduction: {
      coverage:
        "After possibly swapping U,V, V is in one coset mod d and U is in at most two classes mod 36/d, for d in {3,4,6}.",
      byDivisor: reduction.byDivisor,
      enumeratedCandidatePairs,
      acceptedExceptionalPairs,
      traceGramSquareTarget: 936,
      exceptionalSquaredSingularValues: [30, 6]
    },
    affineSetOrbitCount: reduction.representatives.length,
    affineSetOrbitRepresentatives: reduction.representatives,
    gramStarAudit: gramStarAuditResult,
    uniqueFiveGramSurvivor: [0, 6, 12, 18, 24, 30],
    formalBoundary: {
      provesByExhaustion: [
        "The projective-class candidate family has 159516 oriented candidates.",
        "Exactly 1584 candidates have rank at most two and Gram eigenvalues 30,6.",
        "The participating six-point sets have exactly eight affine-or-swap set orbits.",
        "Among those eight orbits, only the affine orbit of 6Z_36 admits five exceptional Gram matrices summing to 30I."
      ],
      mathematicalLemmasRequiredOutsideThisCertificate: [
        "A rank-two unimodular matrix has at most two projective row classes or at most two projective column classes.",
        "For Fourier submatrices of F_36, projective classes are residue classes determined by gcd(36,V-V) and gcd(36,U-U).",
        "The K30 block-Gram identities imply either the common-spectrum branch or the rank-two exceptional branch.",
        "One exceptional block propagates the exceptional branch to all 25 fibre blocks."
      ],
      notClaimed: [
        "No Lean theorem is generated by this certificate.",
        "The certificate does not prove the spectral-to-block-Gram reduction.",
        "The certificate does not prove the subsequent K5 lift or the final Z180 tiling theorem."
      ]
    }
  };
}

const scriptPath = fileURLToPath(import.meta.url);
const scriptDirectory = path.dirname(scriptPath);
let certificatePath = path.join(
  scriptDirectory,
  "z180_k30_exceptional_exact.certificate.json"
);
const certificateFlag = process.argv.indexOf("--certificate");
if (certificateFlag >= 0) {
  assert.ok(process.argv[certificateFlag + 1], "--certificate requires a path");
  certificatePath = path.resolve(process.argv[certificateFlag + 1]);
}

const computed = buildCertificate();
if (process.argv.includes("--print-certificate")) {
  process.stdout.write(JSON.stringify(computed, null, 2) + "\n");
  process.exit(0);
}

const expected = JSON.parse(fs.readFileSync(certificatePath, "utf8"));
assert.deepStrictEqual(computed, expected);

function sha256(bytes) {
  return crypto.createHash("sha256").update(bytes).digest("hex").toUpperCase();
}

const sourceBytes = fs.readFileSync(scriptPath);
const certificateBytes = fs.readFileSync(certificatePath);
process.stdout.write(
  JSON.stringify(
    {
      status: "PASS",
      source: { path: scriptPath, bytes: sourceBytes.length, sha256: sha256(sourceBytes) },
      certificate: {
        path: certificatePath,
        bytes: certificateBytes.length,
        sha256: sha256(certificateBytes)
      },
      enumeratedCandidatePairs: computed.projectiveReduction.enumeratedCandidatePairs,
      acceptedExceptionalPairs: computed.projectiveReduction.acceptedExceptionalPairs,
      affineSetOrbitCount: computed.affineSetOrbitCount,
      uniqueFiveGramSurvivor: computed.uniqueFiveGramSurvivor
    },
    null,
    2
  ) + "\n"
);

