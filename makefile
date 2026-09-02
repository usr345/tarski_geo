.PHONY: graph clean

graph: graph.svg

graph.svg: graph.gv
	dot -Tsvg $< -o $@

clean:
	rm -f graph.svg
