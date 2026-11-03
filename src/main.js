import Plotly from 'plotly.js-dist-min';
import './timeseries-plot.css';
import './mobile.css';

window.Plotly = Plotly;
await import('./timeseries-plot.js');

const params = new URLSearchParams(window.location.search);
window.initialize_timeseries_plot({
   share: params.get('share') || undefined,
   showHelp: true,
   url: params.get('url') || undefined,
   hideMetadata: true,
   hideRecent: false,
   hideTheme: true,
   hideModes: false,
   thumbnail: params.get('thumbnail') || undefined
});

if (import.meta.env.PROD && 'serviceWorker' in navigator) {
   window.addEventListener('load', () => {
      navigator.serviceWorker.register('./sw.js').catch((error) => {
         console.warn('Offline support could not be enabled.', error);
      });
   });
}
