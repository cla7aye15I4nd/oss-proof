# Sharp 和 Pillow 处理不可信图像时真正运行的 C 代码

## 怎么读这一页 {#evidence}

**Tier 0** 指在默认路径上把不可信字节变成像素或元数据的那部分代码，下面每个目标都只证明这一部分。对已解码像素做的编码、缩放和色彩处理不在其中。

这里没有任何一条来自包描述：在 Linux x86_64 上用 npm 安装 `sharp@0.35.5`、用 PyPI 安装 Pillow 13.0.0，确认实际打包了哪些库；调用链中的每个函数名都在各上游仓库最新源码中查过，每个文件名都链接到对应源码。

决定能否到达的是两个事实：Sharp 用 `vips_foreign_find_load_buffer` 选择加载器，Pillow 的 `Image.open` 会逐个尝试所有已注册插件。两者都只看文件开头的魔数，从不看文件名，所以**它们启用的每一个解码器都能被上传的文件触达**。

## 调用链 {#explorer}

在图上方选择一条调用链。每条链都从普通的应用代码出发，一直追到解析这些字节的 C 库。蓝色是 Tier 0 目标，绿色是已有进度记录的项目，灰色虚线是在路径上但不计划证明的部分。

[[audit-explorer]]

## Tier 0 目标 {#targets}

| 库 | 由谁触达 | 状态 |
| --- | --- | --- |
| libvips：格式识别、加载器衔接代码、内置 GIF 解码器、EXIF 与 ICC 衔接代码 | Sharp 的每一次调用 | 未完成 |
| mozjpeg | Sharp 的 JPEG、TIFF 中的 JPEG | 未完成 |
| libpng | Sharp 的 PNG | 未完成 |
| libwebp | Sharp 与 Pillow 的 WebP | 未完成 |
| libtiff | Sharp 与 Pillow 的 TIFF | 未完成 |
| libexif | Sharp 中每个带 EXIF 的输入 | 未完成 |
| lcms2 | Sharp 中每个带 ICC 配置的输入 | 未完成 |
| libxml2 | Sharp 的 SVG | 未完成 |
| Pillow 的 `libImaging` 解码器 | Pillow 的每次 `load()` | 未完成 |
| libjpeg-turbo | Pillow 的 JPEG、TIFF 中的 JPEG | 未完成 |
| libavif | Pillow 的 AVIF | 未完成 |
| openjpeg | Pillow 的 JPEG 2000 | 未完成 |
| liblzma（xz） | Pillow 的 LZMA 压缩 TIFF、Python 的 `lzma` 模块 | 未完成 |
| zlib-ng | Sharp 与 Pillow 的 PNG、Deflate 压缩 TIFF | [已有进度记录](../zlib-ng/zh/progress.html) |
| bzip2、lz4 | Python 的 `bz2` 模块、python-lz4、libarchive（不在 Sharp 与 Pillow 路径上） | 未完成 |

zlib、zstd、brotli、7-Zip SDK 与 libarchive 保持各自原有范围，这里不再重复。

## 核对后排除的库 {#excluded}

| 库 | 不作为目标的原因 |
| --- | --- |
| libspng | Sharp 所用的 libvips 以 `-Dspng=disabled` 构建；Pillow 也不使用 |
| expat | 在 Sharp 中只读取从路径打开的 `.vips` 文件与 fontconfig 配置；Pillow 没有打包它 |
| FreeType | 渲染的是应用选定的字体，而不是上传的字体 |
| cgif、libimagequant | 属于 Sharp 的 GIF 编码路径，输入已是解码后的像素，不属于 Tier 0 |
| librsvg | Rust 实现；它解析 XML 所用的 C 库 libxml2 已列为目标 |
| libheif、aom、dav1d | C++ 实现或体量很大的 AV1 编解码器，暂缓 |
