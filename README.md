## Welcome to XPlot

**XPlot** is a time series data web app.

![image](https://user-images.githubusercontent.com/805898/140074187-69517649-ccc5-4638-b12c-1dd774afe49f.png)

### History
**XPlot** was initially created as hobby project with the following base requirements in mind.

1. Create a pure Javascript/HTML/CSS web app for plotting data.
2. Support plotting of time series data from CSV files.
3. Use **plotly** as the graph renderer (plotly is the only external dependency).
4. No backend or server required. All data is stored locally in your browser.
5. Make it an **Progressive Web App** (PWA, see https://pwabuilder.com for more info).

Since the start **Xplot** has grown in features, but still remain true to the intial requirements.

### How can I run/install XPlot?

After this repository is published, XPlot is served from GitHub Pages: https://izaxon.github.io/xplot/

Open the menu and choose **Open...**, then pick a CSV file. The first column is the timestamp and each following column is a series. A small example is included at `public/samples/harbor-weather.csv`. You can also drop a file onto the plot, or paste CSV text.

XPlot runs in current desktop and mobile browsers. It can be installed from the browser (Add to Home Screen / Install app). Plots stay in this browser; nothing is uploaded.

### Run locally

Requires Node.js 22 or newer.

```bash
npm install
npm run dev
```

The dev server prints a local URL. `npm run build` writes the static site to `dist/`, and `npm run preview` serves that build.

### Deployment

GitHub Pages for this repository is published from the `gh-pages` branch. Pushing to `main` runs `.github/workflows/pages.yml`, which builds the site and updates that branch. The workflow needs repository Actions permission to write contents.

### Can I report bugs or request new features?

Yes! Please visit [issues](https://github.com/izaxon/xplot/issues) and create a new issue.

### Finally

Thanks trying out using XPlot!

More will follow...

J

-----
### Blog
#### 2021-12-15 [Why is XPlot a Progressive Web App (PWA)?](why_pwa.md)
