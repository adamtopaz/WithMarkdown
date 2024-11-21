import React, { useEffect, useRef } from 'react';
import remarkMath from 'remark-math'
import Markdown from 'react-markdown';

// @ts-ignore
import rehypeMathjax from 'rehype-mathjax'

interface MarkdownViewerProps {
    src: string;
}

const MarkdownViewer = ({ src }: MarkdownViewerProps) => {
    const ref = useRef<HTMLDivElement>(null);

    useEffect(() => {
        if (ref.current) {
            ref.current.querySelectorAll('pre code').forEach((block) => {
                // @ts-ignore
                hljs.highlightBlock(block);
            });
        }
    }, [src]);

    return (
        <div ref={ref}>
            <Markdown
                remarkPlugins={[remarkMath]}
                rehypePlugins={[rehypeMathjax]}
                children={src}
            />
        </div>
    );
}

export default MarkdownViewer;