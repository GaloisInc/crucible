all: do-it

DOCKER_TAG=svcomp-runner:latest
BENCH_DEFS_DIR=/home/rscott2/bench-defs

do-it:
	docker build . -t $(DOCKER_TAG)
	docker run --rm -i -t --privileged \
	           --volume=/sys/fs/cgroup:/sys/fs/cgroup:rw \
			   --volume=$(BENCH_DEFS_DIR):/home/bench-defs \
			   --workdir=/home/bench-defs \
			   $(DOCKER_TAG) bash
