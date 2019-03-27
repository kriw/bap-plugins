for l in copypropagation mydeadcode myssa prunessa; do
    make -C $l clean
    make -C $l all
done
