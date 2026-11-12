N=$1; G=https://storage.googleapis.com/brain-genomics-public/research/sequencing/fastq/novaseq/wgs_pcr_free/30x/HG002.novaseq.pcr-free.30x
s=$(date +%s.%N)
for m in 1 2; do (curl -sS $G.R$m.fastq.gz 2>/dev/null | gunzip -c 2>/dev/null | head -n $((4*N)) > /dev/null) & done; wait
e=$(date +%s.%N); echo "raw N=$N: $(echo "$e-$s"|bc) s wall, $(echo "$N/($e-$s)"|bc) pairs/s"
