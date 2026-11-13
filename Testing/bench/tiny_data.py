#!/usr/bin/env python3
"""Small test data with a known answer.   tiny_data.py OUTDIR
Writes OUTDIR/genome.fa, reads_R1.fq.gz, reads_R2.fq.gz. No download.

1. Genome: 4 Mb in 5 chromosomes, random, but every 15-letter word occurs once on both strands
   (each next letter is drawn among those whose new word is unused; a word and its reverse complement
   are always marked used together, so the reverse complement is then unused too).
2. Pairs: every 40 letters a fragment of about 400 starts; it gives two pairs, one per orientation, 2x150,
   all qualities 'I', with 0-2 substitutions per mate. The name holds the true position (tiny_truth.py checks it).
3. Pairs our adapter rule would cut are left out (the adapter AGATCGGAAGAGC with at most 1 mismatch, or its
   first 6+ letters at the read's end; Spec/Trim.lean `cut`). minibwa does not cut, so those would differ.
On this data both tools must give the same alignment for every pair."""
import gzip
import random
import sys

assert len(sys.argv) == 2, __doc__
out = sys.argv[1]
K = 15                                     # word length
LENGTHS = [1_200_000, 900_000, 800_000, 600_000, 500_000]
READ_LENGTH = 150
STEP = 40                                  # a fragment starts every STEP letters

# ---- 1. genome ----
# A word of K letters is a number of 2K bits (A=0, C=1, G=2, T=3). `used` has one bit per possible word.
used = bytearray(2 ** (2 * K) // 8)
WORD_MASK = 2 ** (2 * K) - 1


def is_used(word):
    return (used[word // 8] >> (word % 8)) & 1 == 1


def mark_used(word):
    used[word // 8] = used[word // 8] | (1 << (word % 8))


def append_to_forward(word, letter):
    """The word that follows `word` when `letter` is added at its end."""
    return ((word << 2) | letter) & WORD_MASK


def prepend_to_reverse(word, letter):
    """The reverse complement of the word above: the complement of `letter` comes in at the front."""
    return (word >> 2) | ((3 - letter) << (2 * (K - 1)))


rng = random.Random(1)
chroms = {}
for number, length in enumerate(LENGTHS):
    letters = [rng.randrange(4) for _ in range(K - 1)]
    forward = 0                            # the word at the end of the chromosome so far, and its reverse complement
    reverse = 0
    for letter in letters:
        forward = append_to_forward(forward, letter)
        reverse = prepend_to_reverse(reverse, letter)
    for _ in range(length - K + 1):
        order = [0, 1, 2, 3]
        rng.shuffle(order)
        chosen = None
        for letter in order:
            if not is_used(append_to_forward(forward, letter)):
                chosen = letter
                break
        if chosen is None:
            sys.exit("dead end: all four next letters make a word that is used already")
        forward = append_to_forward(forward, chosen)
        reverse = prepend_to_reverse(reverse, chosen)
        assert forward != reverse and not is_used(reverse)
        mark_used(forward)
        mark_used(reverse)
        letters.append(chosen)
    chroms["chrU" + str(number + 1)] = "".join("ACGT"[letter] for letter in letters)
with open(out + "/genome.fa", "w") as genome_file:
    for name, sequence in chroms.items():
        genome_file.write(">" + name + "\n")
        for line_start in range(0, len(sequence), 60):
            genome_file.write(sequence[line_start:line_start + 60] + "\n")

# ---- 2. and 3. pairs ----
rng = random.Random(7)
ADAPTER = "AGATCGGAAGAGC"


def is_cut(read):
    """Would our adapter rule cut this read?"""
    for i in range(len(read)):
        rest = read[i:]
        if len(rest) >= len(ADAPTER):
            mismatches = sum(a != b for a, b in zip(ADAPTER, rest))
            if mismatches <= 1:
                return True
        elif len(rest) >= 6 and rest == ADAPTER[:len(rest)]:
            return True
    return False


def reverse_complement(s):
    return s[::-1].translate(str.maketrans("ACGT", "TGCA"))


def mutate(read, count):
    """`count` substitutions at random places, none within 20 letters of an end."""
    read = list(read)
    for place in rng.sample(range(20, READ_LENGTH - 20), count):
        read[place] = rng.choice([letter for letter in "ACGT" if letter != read[place]])
    return "".join(read)


SUBSTITUTIONS = [(0, 0), (1, 1), (2, 2), (1, 0), (0, 2), (2, 1)]     # (in mate 1, in mate 2), used in turn
QUALITY = "I" * READ_LENGTH
made = 0
kept = 0
with gzip.open(out + "/reads_R1.fq.gz", "wt", compresslevel=1) as file1, \
        gzip.open(out + "/reads_R2.fq.gz", "wt", compresslevel=1) as file2:
    for chrom, sequence in chroms.items():
        for start in range(0, len(sequence) - 500, STEP):
            fragment_length = min(500, max(300, round(rng.gauss(400, 40))))
            fragment = sequence[start:start + fragment_length]
            first_read = fragment[:READ_LENGTH]                                       # forward, at `start`
            last_read = reverse_complement(fragment[-READ_LENGTH:])                   # reverse, at the fragment's end
            for strand in "+-":
                if strand == "+":
                    mate1, mate2 = first_read, last_read
                else:
                    mate1, mate2 = last_read, first_read
                subs1, subs2 = SUBSTITUTIONS[made % len(SUBSTITUTIONS)]
                mate1 = mutate(mate1, subs1)
                mate2 = mutate(mate2, subs2)
                name = "u" + str(made) + "_" + chrom + "_" + str(start) + "_" + str(fragment_length) + "_" + strand \
                    + "_" + str(subs1) + "_" + str(subs2)
                made += 1
                if is_cut(mate1) or is_cut(mate2):
                    continue
                file1.write("@" + name + "/1\n" + mate1 + "\n+\n" + QUALITY + "\n")
                file2.write("@" + name + "/2\n" + mate2 + "\n+\n" + QUALITY + "\n")
                kept += 1
print(kept, "pairs written,", made - kept, "left out (adapter rule)")
